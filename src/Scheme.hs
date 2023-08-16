{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}

module Scheme where

import Control.Monad ((>=>))
import Data.Bifunctor (Bifunctor (first))
import Data.Foldable (foldrM)
import Data.Map (Map)
import Data.Map qualified as Map

type Proc = [Value 'Evaluate] -> Either SchemeError (Value 'Evaluate)

type Env = Map String (Value 'Evaluate)

data Stage = Interpret | Evaluate

data Value (s :: Stage) where
  Bool :: Bool -> Value s
  Char :: Char -> Value s
  Null :: Value s
  Number :: Int -> Value s
  Pair :: Value s -> Value s -> Value s
  Symbol :: String -> Value s
  Builtin :: Proc -> Value 'Evaluate
  Lambda :: [String] -> Maybe String -> Expr -> Value 'Evaluate

castValue :: Value 'Interpret -> Value 'Evaluate
castValue = \case
  Bool b -> Bool b
  Char c -> Char c
  Null -> Null
  Number n -> Number n
  Pair a b -> Pair (castValue a) (castValue b)
  Symbol s -> Symbol s

instance Show (Value s) where
  show = \case
    Bool b -> "Bool " <> show b
    Char c -> "Char " <> show c
    Null -> "Null"
    Number n -> "Number " <> show n
    Pair a b -> "Pair (" <> show a <> ") (" <> show b <> ")"
    Symbol s -> "Symbol " <> show s
    Builtin _ -> "Builtin"
    Lambda{} -> "Lambda"

instance Eq (Value s) where
  Bool a == Bool b = a == b
  Char a == Char b = a == b
  Null == Null = True
  Number a == Number b = a == b
  Pair a b == Pair c d = a == c && b == d
  Symbol a == Symbol b = a == b
  _ == _ = False

data Expr where
  Var :: String -> Expr
  Value :: Value 'Evaluate -> Expr
  Call :: Expr -> [Expr] -> Expr
  If :: Expr -> Expr -> (Maybe Expr) -> Expr
  deriving (Eq, Show)

list :: [Value s] -> Value s
list = foldr Pair Null

quote :: Value s -> Value s
quote d = list [Symbol "quote", d]

specials :: Map String ([Value 'Interpret] -> Either SchemeError Expr)
specials =
  Map.fromList
    [
      ( "quote"
      , \case
          [a] -> Right (Value $ castValue a)
          args -> Left (WrongNumArgs "quote" (castValue <$> args))
      )
    ,
      ( "if"
      , \case
          args@(tst : t : f) ->
            If <$> interpret tst <*> interpret t <*> case f of
              [] -> Right Nothing
              [e] -> Just <$> interpret e
              _ -> Left (WrongNumArgs "if" (castValue <$> args))
          args -> Left (WrongNumArgs "if" (castValue <$> args))
      )
    ,
      ( "lambda"
      , \case
          (args : body) ->
            case interpretImproperList args of
              (args', var) ->
                Value
                  <$> ( Lambda
                          <$> traverse
                            ( \case
                                Symbol s -> Right s
                                _ -> Left BadVar
                            )
                            args'
                          <*> ( case var of
                                  Null -> Right Nothing
                                  Symbol s -> Right (Just s)
                                  _ -> Left BadVar
                              )
                          <*> ( case body of
                                  [b] -> interpret b
                                  _ -> 
                                    Left $ BadArgs "lambda" (castValue <$> body)
                              )
                      )
          [] -> Left (WrongNumArgs "lambda" [])
      )
    ]

procs :: Map String Proc
procs =
  Map.fromList
    [ unary "car" $
        \case
          Pair a _ -> Just a
          _ -> Nothing
    , unary "cdr" $ \case
        Pair _ b -> Just b
        _ -> Nothing
    ,
      ( "cons"
      , \case
          [a, b] -> Right (Pair a b)
          args -> Left (BadArgs "cons" args)
      )
    , unary "null?" $ \case
        Null -> Just (Bool True)
        _ -> Just (Bool False)
    ,
      ( "+"
      , \args ->
          foldrM
            (\a b -> maybe (Left $ BadArgs "+" args) Right $ add a b)
            (Number 0)
            args
      )
    ]
 where
  unary ::
    String ->
    (Value 'Evaluate -> Maybe (Value 'Evaluate)) ->
    (String, Proc)
  unary name f =
    ( name
    , \case
        [a] -> maybe (Left $ BadArgs name [a]) Right (f a)
        args -> Left (WrongNumArgs name args)
    )

  add :: Value 'Evaluate -> Value 'Evaluate -> Maybe (Value 'Evaluate)
  add (Number a) (Number b) = Just (Number (a + b))
  add _ _ = Nothing

data SchemeError where
  NotInScope :: String -> SchemeError
  ArgsNotAList :: SchemeError
  ApplyingNonProc :: SchemeError
  WrongNumArgs :: String -> [Value 'Evaluate] -> SchemeError
  BadArgs :: String -> [Value 'Evaluate] -> SchemeError
  Undefined :: SchemeError
  BadVar :: SchemeError
  deriving (Eq, Show)

interpret :: Value 'Interpret -> Either SchemeError Expr
interpret (Symbol s) = Right (Var s)
interpret (Pair p args) = do
  args' <- interpretList args
  case p of
    Symbol s -> maybe (mkCall p args') ($ args') (Map.lookup s specials)
    _ -> mkCall p args'
 where
  mkCall :: Value 'Interpret -> [Value 'Interpret] -> Either SchemeError Expr
  mkCall p' args' = Call <$> interpret p' <*> traverse interpret args'
interpret d = Right (Value $ castValue d)

interpretImproperList :: Value s -> ([Value s], Value s)
interpretImproperList (Pair a b) = first (a :) (interpretImproperList b)
interpretImproperList d = ([], d)

interpretList :: Value s -> Either SchemeError [Value s]
interpretList v = case interpretImproperList v of
  (args, Null) -> Right args
  _ -> Left ArgsNotAList

evaluate :: Env -> Expr -> Either SchemeError (Value 'Evaluate)
evaluate e (Var s) =
  maybe (Left $ NotInScope s) Right (Map.lookup s e)
evaluate _ (Value d) = Right d
evaluate e (Call p args) = do
  p' <- evaluate e p
  args' <- traverse (evaluate e) args
  case p' of
    Builtin f -> f args'
    Lambda args'' var body -> do
      e' <- zipArgs args'' args' var
      evaluate (e' <> e) body
    _ -> Left ApplyingNonProc
evaluate e (If tst t f) = do
  tst' <- evaluate e tst
  if tst' /= Bool False
    then evaluate e t
    else case f of
      Nothing -> Left Undefined
      Just f' -> evaluate e f'

zipArgs :: [String] -> [Value 'Evaluate] -> Maybe String -> Either SchemeError Env
zipArgs [] [] mv =
  Right $ Map.empty <> maybe Map.empty (\v -> Map.singleton v (list [])) mv
zipArgs (s : ss) (a : as) v = Map.insert s a <$> zipArgs ss as v
zipArgs [] as (Just v) = Right $ Map.singleton v (list as)
zipArgs [] as Nothing = Left (WrongNumArgs "lambda" as)
zipArgs (_:_) [] _ = Left (WrongNumArgs "lambda" [])

execute :: Value 'Interpret -> Either SchemeError (Value 'Evaluate)
execute = interpret >=> evaluate (Builtin <$> procs)
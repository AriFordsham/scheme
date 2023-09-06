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

type Proc = [ValueExt] -> Either SchemeError ValueExt

type Env = Map String ValueExt

data Stage = Interpret | Evaluate

newtype SType = SType Bool

data ValueExt = forall ty. ValueExt (Value ty 'Evaluate)

instance Eq ValueExt where
  (ValueExt a) == (ValueExt b) = valEq a b

instance Show ValueExt where
  show (ValueExt a) = show a

data Value (ty :: SType) (s :: Stage) where
  Bool :: Bool -> Value ('SType 'False) s
  Char :: Char -> Value ('SType 'False) s
  Null :: Value ('SType 'False) s
  Number :: Int -> Value ('SType 'False) s
  Pair :: Value a s -> Value b s -> Value ('SType 'False) s
  Symbol :: String -> Value ('SType 'False) s
  Builtin :: Proc -> Value ('SType 'True) 'Evaluate
  Lambda :: [String] -> Maybe String -> Expr -> Value ('SType 'True) 'Evaluate
  CastProc :: Value ty 'Evaluate -> Value ('SType 'True) 'Evaluate

instance Eq (Value ty s) where
  (==) = valEq

valEq :: Value a s -> Value b s -> Bool
valEq a b = case (a, b) of
  (Bool a', Bool b') -> a' == b'
  (Char a', Char b') -> a' == b'
  (Null, Null) -> True
  (Number a', Number b') -> a' == b'
  (Pair la lb, Pair ra rb) -> valEq la ra && valEq lb rb
  (Symbol a', Symbol b') -> a' == b'
  (_, _) -> False

castValue :: Value ty 'Interpret -> Value ('SType 'False) s
castValue = \case
  Bool b -> Bool b
  Char c -> Char c
  Null -> Null
  Number n -> Number n
  Pair a b -> Pair (castValue a) (castValue b)
  Symbol s -> Symbol s

instance Show (Value ty s) where
  show = \case
    Bool b -> "Bool " <> show b
    Char c -> "Char " <> show c
    Null -> "Null"
    Number n -> "Number " <> show n
    Pair a b -> "Pair (" <> show a <> ") (" <> show b <> ")"
    Symbol s -> "Symbol " <> show s
    Builtin _ -> "Builtin"
    Lambda{} -> "Lambda"
    CastProc _ -> "CastProc"

data Expr where
  Var :: String -> Expr
  Value :: Value ty 'Evaluate -> Expr
  Call :: Expr -> [Expr] -> Expr
  If :: Expr -> Expr -> (Maybe Expr) -> Expr

-- deriving (Eq, Show)

list :: [Value ('SType 'False) a] -> Value ('SType 'False) a
list = foldr Pair Null

list' :: [ValueExt] -> ValueExt
list' = ValueExt . foldr (\(ValueExt v) -> Pair v) Null

quote :: Value ('SType 'False) 'Interpret -> Value ('SType 'False) 'Interpret
quote d = list [Symbol "quote", d]

lambda :: [String] -> Value ('SType 'False) 'Interpret -> Value ('SType 'False) 'Interpret
lambda args body =
  list
    [ Symbol "lambda"
    , list $ Symbol <$> args
    , body
    ]

specials :: Map String ([Value ('SType 'False) 'Interpret] -> Either SchemeError Expr)
specials =
  Map.fromList
    [
      ( "quote"
      , \case
          [a] -> Right (Value $ castValue a)
          args -> Left (WrongNumArgs "quote" (ValueExt . castValue <$> args))
      )
    ,
      ( "if"
      , \case
          args@(tst : t : f) ->
            If <$> interpret tst <*> interpret t <*> case f of
              [] -> Right Nothing
              [e] -> Just <$> interpret e
              _ -> Left (WrongNumArgs "if" (ValueExt . castValue <$> args))
          args -> Left (WrongNumArgs "if" (ValueExt . castValue <$> args))
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
                                    Left $ BadArgs "lambda" (ValueExt . castValue <$> body)
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
          ValueExt (Pair a _) -> Just (ValueExt a)
          _ -> Nothing
    , unary "cdr" $ \case
        ValueExt (Pair _ b) -> Just (ValueExt b)
        _ -> Nothing
    ,
      ( "cons"
      , \case
          [ValueExt a, ValueExt b] -> Right (ValueExt $ Pair a b)
          args -> Left (BadArgs "cons" args)
      )
    , unary "null?" $ \case
        ValueExt Null -> Just (ValueExt $ Bool True)
        _ -> Just (ValueExt $ Bool False)
    ,
      ( "+"
      , \args ->
          foldrM
            (\(ValueExt a) (ValueExt b) -> maybe (Left $ BadArgs "+" args) (Right . ValueExt) $ add a b)
            (ValueExt $ Number 0)
            args
      )
    ,
      ( "list"
      , Right . list'
      )
    ]
 where
  unary ::
    String ->
    (ValueExt -> Maybe ValueExt) ->
    (String, Proc)
  unary name f =
    ( name
    , \case
        [a] -> maybe (Left $ BadArgs name [a]) Right (f a)
        args -> Left (WrongNumArgs name args)
    )

  add :: Value l 'Evaluate -> Value r 'Evaluate -> Maybe (Value ('SType 'False) 'Evaluate)
  add (Number a) (Number b) = Just (Number (a + b))
  add _ _ = Nothing

data SchemeError where
  NotInScope :: String -> SchemeError
  ArgsNotAList :: SchemeError
  ApplyingNonProc :: SchemeError
  WrongNumArgs :: String -> [ValueExt] -> SchemeError
  BadArgs :: String -> [ValueExt] -> SchemeError
  Undefined :: SchemeError
  BadVar :: SchemeError
  deriving (Eq, Show)

interpret :: Value ('SType 'False) 'Interpret -> Either SchemeError Expr
interpret (Symbol s) = Right (Var s)
interpret (Pair p args) = do
  args' <- interpretList (castValue args)
  case p of
    Symbol s -> maybe (mkCall p args') ($ args') (Map.lookup s specials)
    _ -> mkCall (castValue p) args'
 where
  mkCall :: Value ('SType 'False) 'Interpret -> [Value ('SType 'False) 'Interpret] -> Either SchemeError Expr
  mkCall p' args' = Call <$> interpret p' <*> traverse interpret args'
interpret d = Right (Value $ castValue d)

interpretImproperList :: Value ('SType 'False) 'Interpret -> ([Value ('SType 'False) 'Interpret], Value ('SType 'False) 'Interpret)
interpretImproperList (Pair a b) = first (castValue a :) (interpretImproperList (castValue b))
interpretImproperList d = ([], d)

interpretList :: Value ('SType 'False) 'Interpret -> Either SchemeError [Value ('SType 'False) 'Interpret]
interpretList v = case interpretImproperList v of
  (args, Null) -> Right args
  _ -> Left ArgsNotAList

evaluate :: Env -> Expr -> Either SchemeError ValueExt
evaluate e (Var s) =
  maybe (Left $ NotInScope s) Right (Map.lookup s e)
evaluate _ (Value d) = Right (ValueExt d)
evaluate e (Call p args) = do
  (ValueExt p') <- evaluate e p
  args' <- traverse (evaluate e) args
  case p' of
    Builtin f -> f args'
    Lambda args'' var body -> do
      e' <- zipArgs args'' args' var
      evaluate (e' <> e) body
    _ -> Left ApplyingNonProc
evaluate e (If tst t f) = do
  (ValueExt tst') <- evaluate e tst
  case tst' of
    Bool False -> case f of
      Nothing -> Left Undefined
      Just f' -> evaluate e f'
    _ -> evaluate e t

zipArgs :: [String] -> [ValueExt] -> Maybe String -> Either SchemeError Env
zipArgs [] [] mv =
  Right $ Map.empty <> maybe Map.empty (\v -> Map.singleton v (list' [])) mv
zipArgs (s : ss) (a : as) v = Map.insert s a <$> zipArgs ss as v
zipArgs [] as (Just v) = Right $ Map.singleton v (list' as)
zipArgs [] as Nothing = Left (WrongNumArgs "lambda" as)
zipArgs (_ : _) [] _ = Left (WrongNumArgs "lambda" [])

execute :: Value ('SType 'False) 'Interpret -> Either SchemeError ValueExt
execute = interpret >=> evaluate (ValueExt . Builtin <$> procs)
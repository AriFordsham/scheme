{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}

module Scheme where

import Control.Monad ((>=>))
import Data.Coerce (coerce)
import Data.Foldable (foldrM)
import Data.Map (Map)
import Data.Map qualified as Map

type Proc = [Value 'Evaluate] -> Either SchemeError (Value 'Evaluate)

data Stage = Interpret | Evaluate

data Value (s :: Stage) where
  Bool :: Bool -> Value s
  Char :: Char -> Value s
  Null :: Value s
  Number :: Int -> Value s
  Pair :: Value s -> Value s -> Value s
  Symbol :: String -> Value s
  Builtin :: Proc -> Value 'Evaluate

instance Show (Value s) where
  show = \case
    Bool b -> "Bool " <> show b
    Char c -> "Char " <> show c
    Null -> "Null"
    Number n -> "Number " <> show n
    Pair a b -> "Pair (" <> show a <> ") (" <> show b <> ")"
    Symbol s -> "Symbol " <> show s
    Builtin _ -> "Builtin"

instance Eq (Value s) where
  Bool a == Bool b = a == b
  Char a == Char b = a == b
  Null == Null = True
  Number a == Number b = a == b
  Pair a b == Pair c d = a == c && b == d
  Symbol a == Symbol b = a == b
  Builtin _ == Builtin _ = False
  _ == _ = False

data Expr where
  Var :: String -> Expr
  Value :: (forall s. Value s) -> Expr
  Call :: Expr -> [Expr] -> Expr
  If :: Expr -> Expr -> (Maybe Expr) -> Expr

deriving instance Show Expr
instance Eq Expr

list :: [Value s] -> Value s
list = foldr Pair Null

quote :: Value s -> Value s
quote d = list [Symbol "quote", d]

specials :: Map String ([forall s. Value s] -> Either SchemeError Expr)
specials =
  Map.fromList
    [
      ( "quote"
      , \case
          [a] -> Right (Value a)
          args -> Left (WrongNumArgs "quote" args)
      )
    ,
      ( "if"
      , \case
          args@(tst : t : f) ->
            If <$> interpret tst <*> interpret t <*> case f of
              [] -> Right Nothing
              [e] -> Just <$> interpret e
              _ -> Left (WrongNumArgs "if" args)
          args -> Left (WrongNumArgs "if" args)
      )
    ]

procs :: Map String (Value 'Evaluate)
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
      , Builtin $ \case
          [a, b] -> Right (Pair a b)
          args -> Left (BadArgs "cons" args)
      )
    , unary "null?" $ \case
        Null -> Just (Bool True)
        _ -> Just (Bool False)
    ,
      ( "+"
      , Builtin $ \args ->
          foldrM
            (\a b -> maybe (Left $ BadArgs "+" args) Right $ add a b)
            (Number 0)
            args
      )
    ]
 where
  unary :: String -> (Value 'Evaluate -> Maybe (Value 'Evaluate)) -> (String, Value 'Evaluate)
  unary name f =
    ( name
    , Builtin $ \case
        [a] -> maybe (Left $ BadArgs name [a]) Right (f a)
        args -> Left (WrongNumArgs name args)
    )

  add :: Value 'Evaluate -> Value 'Evaluate -> Maybe (Value 'Evaluate)
  add (Number a) (Number b) = Just (Number (a + b))
  add _ _ = Nothing

data SchemeError where
  NoSuchProc :: String -> SchemeError
  ArgsNotAList :: SchemeError
  ApplyingNonProc :: SchemeError
  WrongNumArgs :: String -> [Value s] -> SchemeError
  BadArgs :: String -> [Value 'Evaluate] -> SchemeError
  Undefined :: SchemeError

deriving instance Show SchemeError

interpret :: (forall s. Value s) -> Either SchemeError Expr
interpret (Symbol s) = Right (Var s)
interpret (Pair p args) = do
  args' <- interpretList args
  case p of
    Symbol s -> maybe (mkCall p args') ($ args') (Map.lookup s specials)
    _ -> mkCall p args'
 where
  mkCall :: (forall s. Value s) -> [forall s. Value s] -> Either SchemeError Expr
  mkCall p' args' = Call <$> interpret p' <*> traverse interpret args'
interpret d = Right (Value d)

interpretList :: (forall s. Value s) -> Either SchemeError [forall s. Value s]
interpretList Null = Right []
interpretList (Pair a b) = (a :) <$> interpretList b
interpretList _ = Left ArgsNotAList

evaluate :: Expr -> Either SchemeError (Value 'Evaluate)
evaluate (Var s) = maybe (Left $ NoSuchProc s) Right (Map.lookup s procs)
evaluate (Value d) = Right (coerce d)
evaluate (Call p args) = do
  p' <- evaluate p
  args' <- traverse evaluate args
  case p' of
    Builtin f -> f args'
    _ -> Left ApplyingNonProc
evaluate (If tst t f) = do
  tst' <- evaluate tst
  if tst' /= Bool False
    then evaluate t
    else case f of
      Nothing -> Left Undefined
      Just f' -> evaluate f'

execute :: (forall s. Value s) -> Either SchemeError (Value 'Evaluate)
execute = interpret >=> evaluate
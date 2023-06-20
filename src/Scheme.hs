{-# LANGUAGE LambdaCase #-}

module Scheme where

import Control.Monad ((>=>))
import Data.Foldable (foldl', foldrM)
import Data.Map (Map)
import Data.Map qualified as Map

type Proc = [Value] -> Either InterpretError Value

data Value
  = Bool Bool
  | Char Char
  | Null
  | Number Int
  | Pair Value Value
  | Symbol String
  | Builtin Proc

instance Show Value where
  show = \case
    Bool b -> "Bool " <> show b
    Char c -> "Char " <> show c
    Null -> "Null"
    Number n -> "Number " <> show n
    Pair a b -> "Pair (" <> show a <> ") (" <> show b <> ")"
    Symbol s -> "Symbol " <> show s
    Builtin _ -> "Builtin"

instance Eq Value where
  Bool a == Bool b = a == b
  Char a == Char b = a == b
  Null == Null = True
  Number a == Number b = a == b
  Pair a b == Pair c d = a == c && b == d
  Symbol a == Symbol b = a == b
  Builtin _ == Builtin _ = False
  _ == _ = False

data Expr
  = Var String
  | Literal Value
  | Call Expr [Expr]
  deriving (Eq, Show)

list :: [Value] -> Value
list = foldr Pair Null

quote :: Value -> Value
quote d = list [Symbol "quote", d]

specials :: Map String ([Value] -> Either InterpretError Expr)
specials =
  Map.fromList
    [
      ( "quote"
      , \case
          [a] -> Right (Literal a)
          args -> Left (WrongNumArgs "quote" args)
      )
    ,
      ( "begin"
      , \args ->
          foldl' (const interpret) (Left $ WrongNumArgs "begin" args) args
      )
    ]

procs :: Map String Value
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
  unary :: String -> (Value -> Maybe Value) -> (String, Value)
  unary name f =
    ( name
    , Builtin $ \case
        [a] -> maybe (Left $ BadArgs name [a]) Right (f a)
        args -> Left (WrongNumArgs name args)
    )

  add :: Value -> Value -> Maybe Value
  add (Number a) (Number b) = Just (Number (a + b))
  add _ _ = Nothing

data InterpretError
  = NoSuchProc String
  | ArgsNotAList
  | ApplyingNonProc
  | WrongNumArgs String [Value]
  | BadArgs String [Value]
  deriving (Eq, Show)

interpret :: Value -> Either InterpretError Expr
interpret (Symbol s) = Right (Var s)
interpret (Pair p args) = do
  args' <- interpretList args
  case p of
    Symbol s -> maybe (mkCall p args') ($ args') (Map.lookup s specials)
    _ -> mkCall p args'
 where
  interpretList :: Value -> Either InterpretError [Value]
  interpretList Null = Right []
  interpretList (Pair a b) = (a :) <$> interpretList b
  interpretList _ = Left ArgsNotAList

  mkCall :: Value -> [Value] -> Either InterpretError Expr
  mkCall p' args' = Call <$> interpret p' <*> traverse interpret args'
interpret d = Right (Literal d)

evaluate :: Expr -> Either InterpretError Value
evaluate (Var s) = maybe (Left $ NoSuchProc s) Right (Map.lookup s procs)
evaluate (Literal d) = Right d
evaluate (Call p args) = do
  p' <- evaluate p
  args' <- traverse evaluate args
  case p' of
    Builtin f -> f args'
    _ -> Left ApplyingNonProc

execute :: Value -> Either InterpretError Value
execute = interpret >=> evaluate
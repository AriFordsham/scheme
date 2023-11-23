{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Scheme (
  Expr (..),
  Value (..),
  ExprEx (ExprEx),
  ValueEx (ValueEx),
  SchemeError (..),
  SType (..),
  Stage (..),
  interpret,
  exprToSing,
  valueToSing,
  list,
  list',
  quote,
  lambda,
  Proc,
  listArg,
) where

import Data.Bifunctor (Bifunctor (first))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe.Singletons
import Data.Singletons.TH (genSingletons, singDecideInstance)

import Nary (Nary, nary)

data SType = Prim | Proc (Maybe SType)
  deriving (Eq)
genSingletons [''SType]
singDecideInstance ''SType

type Proc = [ValueEx] -> Either SchemeError ValueEx

data Stage = Interpret | Evaluate

data ValueEx = forall ty. ValueEx (Value ty 'Evaluate)

instance Eq ValueEx where
  (ValueEx a) == (ValueEx b) = valEq a b

instance Show ValueEx where
  show (ValueEx a) = show a

data Value (ty :: SType) (s :: Stage) where
  Bool :: Bool -> Value 'Prim s
  Char :: Char -> Value 'Prim s
  Null :: Value 'Prim s
  Number :: Int -> Value 'Prim s
  Pair :: Value a s -> Value b s -> Value 'Prim s
  Symbol :: String -> Value 'Prim s
  Builtin :: Proc -> Value ('Proc 'Nothing) 'Evaluate
  Lambda :: [String] -> Maybe String -> Expr mty -> Value ('Proc mty) 'Evaluate

valueToSing :: Value ty 'Evaluate -> SSType ty
valueToSing = \case
  Bool{} -> SPrim
  Char{} -> SPrim
  Null -> SPrim
  Number{} -> SPrim
  Pair{} -> SPrim
  Symbol{} -> SPrim
  Builtin{} -> SProc SNothing
  Lambda _ _ e -> SProc (exprToSing e)

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

castValue :: Value ty 'Interpret -> Value 'Prim s
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

data ExprEx = forall mty. ExprEx (Expr mty)

instance Show ExprEx where
  show (ExprEx e) = "ExprEx " <> show e

instance Eq ExprEx where
  ExprEx e1 == ExprEx e2 = exprEq e1 e2

data Expr (mty :: Maybe SType) where
  Var :: String -> Expr 'Nothing
  Value :: Value ty 'Evaluate -> Expr ('Just ty)
  Call :: Expr ('Just ('Proc mty)) -> [ExprEx] -> Expr mty
  If :: ExprEx -> ExprEx -> (Maybe ExprEx) -> Expr 'Nothing
  Dynamic :: SSType ty -> Expr 'Nothing -> Expr ('Just ty)

exprToSing :: Expr mty -> SMaybe mty
exprToSing = \case
  Var{} -> SNothing
  Value v -> SJust (valueToSing v)
  Call e _ -> case exprToSing e of
    SJust (SProc mty) -> mty
  If{} -> SNothing
  Dynamic ty _ -> SJust ty

instance Show (Expr mty) where
  show = \case
    Var s -> "Var " <> s
    Value v -> "Value " <> show v
    Call p arg -> "Call " <> show p <> " " <> show arg
    If t th e -> "If " <> show t <> " " <> show th <> " " <> show e
    Dynamic _ e -> "Dynamic " <> show e

instance Eq (Expr mty) where
  a == b = exprEq a b

exprEq :: Expr a -> Expr b -> Bool
exprEq (Var a) (Var b) = a == b
exprEq (Value a) (Value b) = valEq a b
exprEq (Call pa arga) (Call pb argb) =
  exprEq pa pb && arga == argb
exprEq (If ta tha ea) (If tb thb eb) = ta == tb && tha == thb && ea == eb
exprEq _ _ = False

list :: [Value 'Prim a] -> Value 'Prim a
list = foldr Pair Null

list' :: [ValueEx] -> Value 'Prim 'Evaluate
list' = foldr (\(ValueEx v) -> Pair v) Null

quote :: Value 'Prim 'Interpret -> Value 'Prim 'Interpret
quote d = list [Symbol "quote", d]

lambda :: [String] -> Value 'Prim 'Interpret -> Value 'Prim 'Interpret
lambda args body =
  list
    [ Symbol "lambda"
    , list $ Symbol <$> args
    , body
    ]

specials ::
  Map String ([Value 'Prim 'Interpret] -> Either SchemeError ExprEx)
specials =
  Map.fromList
    [ special "quote" quote_
    , special "if" if_
    , special "lambda" lambda_
    ]
 where
  special ::
    Nary t (Value 'Prim 'Interpret) (Either SchemeError a) =>
    String ->
    t ->
    (String, [Value 'Prim 'Interpret] -> Either SchemeError a)
  special s f = (s, listArg (ValueEx . castValue) id s f)

  quote_ :: Value 'Prim 'Interpret -> Either SchemeError ExprEx
  quote_ = Right . ExprEx . Value . castValue

  if_ ::
    Value 'Prim 'Interpret ->
    Value 'Prim 'Interpret ->
    Maybe (Value 'Prim 'Interpret) ->
    Either SchemeError ExprEx
  if_ tst t f = do
    tst' <- interpret tst
    t' <- interpret t
    f' <- traverse interpret f
    pure $ ExprEx $ If tst' t' f'

  lambda_ ::
    Value 'Prim 'Interpret ->
    Value 'Prim 'Interpret ->
    Either SchemeError ExprEx
  lambda_ args body = do
    let (args', var) = interpretImproperList args
    (ExprEx body') <- interpret body
    ExprEx . Value
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
              <*> pure body'
          )

listArg ::
  Nary t a b =>
  (a -> ValueEx) ->
  (b -> Either SchemeError c) ->
  String ->
  t ->
  [a] ->
  Either SchemeError c
listArg f g s v args = maybe (wrongNumArgs s $ fmap f args) g (nary v args)

wrongNumArgs :: String -> [ValueEx] -> Either SchemeError a
wrongNumArgs s = Left . WrongNumArgs s

data SchemeError where
  NotInScope :: String -> SchemeError
  ArgsNotAList :: SchemeError
  TypeError :: SchemeError
  WrongNumArgs :: String -> [ValueEx] -> SchemeError
  BadArgs :: String -> [ValueEx] -> SchemeError
  Undefined :: SchemeError
  BadVar :: SchemeError
  deriving (Eq, Show)

interpret :: Value 'Prim 'Interpret -> Either SchemeError ExprEx
interpret (Symbol s) = Right (ExprEx $ Var s)
interpret (Pair p args) = do
  args' <- interpretList (castValue args)
  case p of
    Symbol s ->
      maybe
        (mkCall p args')
        ($ args')
        (Map.lookup s specials)
    _ -> mkCall (castValue p) args'
 where
  mkCall ::
    Value 'Prim 'Interpret ->
    [Value 'Prim 'Interpret] ->
    Either SchemeError ExprEx
  mkCall p' args' = do
    (ExprEx p'') <- interpret p'
    case exprToSing p'' of
      SNothing -> ExprEx <$> mkCall' (Dynamic (SProc SNothing) p'') args'
      SJust SPrim -> Left TypeError
      SJust (SProc{}) -> ExprEx <$> mkCall' p'' args'

  mkCall' ::
    Expr ('Just ('Proc ty)) ->
    [Value 'Prim 'Interpret] ->
    Either SchemeError (Expr ty)
  mkCall' p' args' = Call p' <$> traverse interpret args'
interpret d = Right (ExprEx . Value $ castValue d)

interpretImproperList ::
  Value 'Prim 'Interpret -> ([Value 'Prim 'Interpret], Value 'Prim 'Interpret)
interpretImproperList (Pair a b) =
  first (castValue a :) (interpretImproperList (castValue b))
interpretImproperList d = ([], d)

interpretList ::
  Value 'Prim 'Interpret -> Either SchemeError [Value 'Prim 'Interpret]
interpretList v = case interpretImproperList v of
  (args, Null) -> Right args
  _ -> Left ArgsNotAList

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Scheme where

import Data.Bifunctor (Bifunctor (first))
import Data.Map (Map)
import Data.Map qualified as Map

import Data.Maybe.Singletons
import Data.Singletons.TH (genSingletons)

import Nary (Nary, nary)

data SType = Prim | Proc (Maybe SType)
genSingletons [''SType]

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

instance Eq ExprEx where
  ExprEx a == ExprEx b = exprEq a b

instance Show ExprEx where
  show (ExprEx a) = show a

data Expr (mty :: Maybe SType) where
  Var :: String -> Expr 'Nothing
  Value :: Value ty 'Evaluate -> Expr ('Just ty)
  Call :: Expr ('Just ('Proc mty)) -> [ExprEx] -> Expr mty
  If :: ExprEx -> ExprEx -> (Maybe ExprEx) -> Expr 'Nothing
  CastProc :: Expr mty -> Expr ('Just ('Proc 'Nothing))
  Upcast :: Expr mty -> Expr 'Nothing

exprToSing :: Expr mty -> SMaybe mty
exprToSing = \case
  Var{} -> SNothing
  Value v -> SJust (valueToSing v)
  Call e _ -> case exprToSing e of
    SJust (SProc mty) -> mty
  If{} -> SNothing
  CastProc{} -> SJust (SProc SNothing)
  Upcast{} -> SNothing

instance Show (Expr mty) where
  show = \case
    Var s -> "Var " <> s
    Value v -> "Value " <> show v
    Call p arg -> "Call " <> show p <> " " <> show arg
    If t th e -> "If " <> show t <> " " <> show th <> " " <> show e
    CastProc e -> "CastProc " <> show e
    Upcast e -> "Upcast " <> show e

exprEq :: Expr a -> Expr b -> Bool
exprEq (Var a) (Var b) = a == b
exprEq (Value a) (Value b) = valEq a b
exprEq (Call pa arga) (Call pb argb) = exprEq pa pb && arga == argb
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

specials :: Map String ([Value 'Prim 'Interpret] -> Either SchemeError ExprEx)
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
  if_ tst t f =
    fmap ExprEx $ If <$> interpret tst <*> interpret t <*> traverse interpret f

  lambda_ ::
    Value 'Prim 'Interpret ->
    Value 'Prim 'Interpret ->
    Either SchemeError ExprEx
  lambda_ args body = do
    let (args', var) = interpretImproperList args
    ExprEx body' <- interpret body
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

procs :: Map String Proc
procs =
  Map.fromList
    [ proc' "car" $ \(ValueEx a) -> car_ a
    , proc' "cdr" $ \(ValueEx a) -> cdr_ a
    , proc' "cons" $ \(ValueEx a) (ValueEx b) -> Just (ValueEx $ Pair a b)
    , proc' "null?" $
        Just . ValueEx . Bool . \case
          ValueEx Null -> True
          _ -> False
    ,
      ( "+"
      , \args ->
          toBad "+" args
            . fmap (ValueEx . Number . sum)
            . traverse (\(ValueEx a) -> toNumber a)
            $ args
      )
    , ("list", Right . ValueEx . list')
    ]
 where
  proc' ::
    (Nary t ValueEx (Maybe ValueEx)) =>
    String ->
    t ->
    (String, Proc)
  proc' s f =
    (s,) $ \as -> listArg id (toBad s as) s f as

  toBad :: String -> [ValueEx] -> Maybe b -> Either SchemeError b
  toBad s as = maybe (Left $ BadArgs s as) Right

  car_ :: Value a 'Evaluate -> Maybe ValueEx
  car_ (Pair a _) = Just (ValueEx a)
  car_ _ = Nothing

  cdr_ :: Value a 'Evaluate -> Maybe ValueEx
  cdr_ (Pair _ b) = Just (ValueEx b)
  cdr_ _ = Nothing

  toNumber :: Value a 'Evaluate -> Maybe Int
  toNumber (Number n) = Just n
  toNumber _ = Nothing

data SchemeError where
  NotInScope :: String -> SchemeError
  ArgsNotAList :: SchemeError
  ApplyingNonProc :: SchemeError
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
        (ExprEx <$> mkCall p args')
        ($ args')
        (Map.lookup s specials)
    _ -> ExprEx <$> mkCall (castValue p) args'
 where
  mkCall ::
    Value 'Prim 'Interpret ->
    [Value 'Prim 'Interpret] ->
    Either SchemeError (Expr 'Nothing)
  mkCall p' args' = do
    e' <- interpret p' >>= validateProc
    Call e' <$> traverse interpret args'
interpret d = Right (ExprEx . Value $ castValue d)

validateProc :: ExprEx -> Either SchemeError (Expr ('Just ('Proc 'Nothing)))
validateProc (ExprEx p') =
  case exprToSing p' of
    SNothing -> Right $ CastProc p'
    SJust SPrim -> Left ApplyingNonProc
    SJust (SProc SNothing) -> Right p'
    SJust (SProc (SJust _)) -> Right $ CastProc p'

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

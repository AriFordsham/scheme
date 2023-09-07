{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}

module Scheme where

import Data.Bifunctor (Bifunctor (first))
import Data.Foldable (foldrM)
import Data.Map (Map)
import Data.Map qualified as Map

type Proc = [ValueEx] -> Either SchemeError ValueEx

type Env = Map String ValueEx

data Stage = Interpret | Evaluate

data SType = Prim | Proc

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
  Builtin :: Proc -> Value 'Proc 'Evaluate
  Lambda :: [String] -> Maybe String -> ExprEx -> Value 'Proc 'Evaluate

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

data ExprEx = forall ty. ExprEx (Expr ty)

instance Eq ExprEx where
  ExprEx a == ExprEx b = exprEq a b

instance Show ExprEx where
  show (ExprEx a) = show a

data Expr (ty :: SType) where
  Var :: String -> Expr ty
  Value :: Value ty 'Evaluate -> Expr ty
  Call :: ExprEx -> [ExprEx] -> Expr ty
  If :: ExprEx -> ExprEx -> (Maybe ExprEx) -> Expr ty

instance Show (Expr ty) where
  show = \case
    Var s -> "Var " <> s
    Value v -> "Value " <> show v
    Call p arg -> "Call " <> show p <> " " <> show arg
    If t th e -> "If " <> show t <> " " <> show th <> " " <> show e

exprEq :: Expr a -> Expr b -> Bool
exprEq (Var a) (Var b) = a == b
exprEq (Value a) (Value b) = valEq a b
exprEq (Call pa arga) (Call pb argb) = pa == pb && arga == argb
exprEq (If ta tha ea) (If tb thb eb) = ta == tb && tha == thb && ea == eb
exprEq _ _ = False

list :: [Value 'Prim a] -> Value 'Prim a
list = foldr Pair Null

list' :: [ValueEx] -> ValueEx
list' = ValueEx . foldr (\(ValueEx v) -> Pair v) Null

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
    [
      ( "quote"
      , \case
          [a] -> Right (ExprEx . Value $ castValue a)
          args -> Left (WrongNumArgs "quote" (ValueEx . castValue <$> args))
      )
    ,
      ( "if"
      , \case
          args@(tst : t : f) ->
            fmap ExprEx $
              If <$> interpret tst <*> interpret t <*> case f of
                [] -> Right Nothing
                [e] -> Just <$> interpret e
                _ -> Left (WrongNumArgs "if" (ValueEx . castValue <$> args))
          args -> Left (WrongNumArgs "if" (ValueEx . castValue <$> args))
      )
    ,
      ( "lambda"
      , \case
          (args : body) ->
            case interpretImproperList args of
              (args', var) ->
                fmap ExprEx $
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
                                      Left $
                                        BadArgs
                                          "lambda"
                                          (ValueEx . castValue <$> body)
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
          ValueEx (Pair a _) -> Just (ValueEx a)
          _ -> Nothing
    , unary "cdr" $ \case
        ValueEx (Pair _ b) -> Just (ValueEx b)
        _ -> Nothing
    ,
      ( "cons"
      , \case
          [ValueEx a, ValueEx b] -> Right (ValueEx $ Pair a b)
          args -> Left (BadArgs "cons" args)
      )
    , unary "null?" $ \case
        ValueEx Null -> Just (ValueEx $ Bool True)
        _ -> Just (ValueEx $ Bool False)
    ,
      ( "+"
      , \args ->
          foldrM
            ( \(ValueEx a) (ValueEx b) ->
                maybe (Left $ BadArgs "+" args) (Right . ValueEx) $ add a b
            )
            (ValueEx $ Number 0)
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
    (ValueEx -> Maybe ValueEx) ->
    (String, Proc)
  unary name f =
    ( name
    , \case
        [a] -> maybe (Left $ BadArgs name [a]) Right (f a)
        args -> Left (WrongNumArgs name args)
    )

  add :: Value l 'Evaluate -> Value r 'Evaluate -> Maybe (Value 'Prim 'Evaluate)
  add (Number a) (Number b) = Just (Number (a + b))
  add _ _ = Nothing

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
    Symbol s -> maybe (mkCall p args') ($ args') (Map.lookup s specials)
    _ -> mkCall (castValue p) args'
 where
  mkCall ::
    Value 'Prim 'Interpret ->
    [Value 'Prim 'Interpret] ->
    Either SchemeError ExprEx
  mkCall p' args' =
    fmap ExprEx $
      Call <$> interpret p' <*> traverse interpret args'
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

evaluate :: Env -> Expr ty -> Either SchemeError ValueEx
evaluate e (Var s) =
  maybe (Left $ NotInScope s) Right (Map.lookup s e)
evaluate _ (Value d) = Right (ValueEx d)
evaluate e (Call (ExprEx p) args) = do
  (ValueEx p') <- evaluate e p
  args' <- traverse (\(ExprEx a) -> evaluate e a) args
  case p' of
    Builtin f -> f args'
    Lambda args'' var (ExprEx body) -> do
      e' <- zipArgs args'' args' var
      evaluate (e' <> e) body
    _ -> Left ApplyingNonProc
evaluate e (If (ExprEx tst) (ExprEx t) f) = do
  (ValueEx tst') <- evaluate e tst
  case tst' of
    Bool False -> case f of
      Nothing -> Left Undefined
      Just (ExprEx f') -> evaluate e f'
    _ -> evaluate e t

zipArgs :: [String] -> [ValueEx] -> Maybe String -> Either SchemeError Env
zipArgs [] [] mv =
  Right $ Map.empty <> maybe Map.empty (\v -> Map.singleton v (list' [])) mv
zipArgs (s : ss) (a : as) v = Map.insert s a <$> zipArgs ss as v
zipArgs [] as (Just v) = Right $ Map.singleton v (list' as)
zipArgs [] as Nothing = Left (WrongNumArgs "lambda" as)
zipArgs (_ : _) [] _ = Left (WrongNumArgs "lambda" [])

execute :: Value 'Prim 'Interpret -> Either SchemeError ValueEx
execute e = do
  ExprEx e' <- interpret e
  evaluate (ValueEx . Builtin <$> procs) e'
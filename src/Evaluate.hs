{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Evaluate where

import Data.Map (Map)
import Data.Map qualified as Map

import Data.Type.Equality

import Data.Maybe.Singletons

import Nary
import Scheme

type Env = Map String ValueEx

evaluate :: Env -> ExprEx -> Either SchemeError ValueEx
evaluate e (ExprEx ex) = case exprToSing ex of
  SNothing -> evaluateUntyped e ex
  SJust{} -> ValueEx <$> evaluateTyped e ex

evaluateTyped ::
  Env -> Expr ('Just ty) -> Either SchemeError (Value ty 'Evaluate)
evaluateTyped _ (Value d) = Right d
evaluateTyped e (Call p args) = do
  p' <- evaluateTyped e p
  args' <- traverse (evaluate e) args
  case p' of
    Lambda args'' var body -> do
      e' <- zipArgs args'' args' var
      evaluateTyped (e' <> e) body
evaluateTyped e (Dynamic ty ex) = do
  (ValueEx v) <- evaluateUntyped e ex
  case testEquality ty (valueToSing v) of
    Just Refl -> Right v
    Nothing -> Left TypeError

evaluateUntyped :: Env -> Expr 'Nothing -> Either SchemeError ValueEx
evaluateUntyped e (Var s) = maybe (Left $ NotInScope s) Right (Map.lookup s e)
evaluateUntyped e (Call p args) = do
  p' <- evaluateTyped e p
  args' <- traverse (evaluate e) args
  case p' of
    Builtin f -> f args'
    Lambda args'' var body -> do
      e' <- zipArgs args'' args' var
      evaluateUntyped (e' <> e) body
evaluateUntyped e (If tst t f) = do
  (ValueEx tst') <- evaluate e tst
  case tst' of
    Bool False -> maybe (Right $ ValueEx Null) (evaluate e) f
    _ -> evaluate e t

zipArgs :: [String] -> [ValueEx] -> Maybe String -> Either SchemeError Env
zipArgs [] [] mv =
  Right $
    Map.empty
      <> maybe Map.empty (\v -> Map.singleton v (ValueEx $ list' [])) mv
zipArgs (s : ss) (a : as) v = Map.insert s a <$> zipArgs ss as v
zipArgs [] as (Just v) = Right $ Map.singleton v (ValueEx $ list' as)
zipArgs [] as Nothing = Left (WrongNumArgs "lambda" as)
zipArgs (_ : _) [] _ = Left (WrongNumArgs "lambda" [])

execute :: Value 'Prim 'Interpret -> Either SchemeError ValueEx
execute e = interpret e >>= evaluate (ValueEx . Builtin <$> procs)

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
  proc' :: (Nary t ValueEx (Maybe ValueEx)) => String -> t -> (String, Proc)
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
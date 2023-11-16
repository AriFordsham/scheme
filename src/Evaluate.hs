{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Evaluate where

import Data.Map ( Map )
import Data.Map qualified as Map

import Data.Maybe.Singletons

import Scheme

type Env = Map String ValueEx


evaluate :: Env -> Expr mty -> Either SchemeError ValueEx
evaluate e ex = case exprToSing ex of
  SNothing -> evaluateUntyped e ex
  SJust{} -> ValueEx <$> evaluateTyped e ex

evaluateTyped :: Env -> 
  Expr ('Just ty) -> Either SchemeError (Value ty 'Evaluate)
evaluateTyped _ (Value d) = Right d
evaluateTyped e (Call p args) = do
  p' <- evaluateTyped e p
  args' <- traverse (evaluate e) args
  case p' of
    Lambda args'' var body -> do
      e' <- zipArgs args'' args' var
      evaluateTyped (e' <> e) body
evaluateTyped e (CastProc ex) = do
  (ValueEx v) <- evaluate e ex
  case valueToSing v of
    SProc SNothing -> Right v
    SProc (SJust{}) -> case v of
      Lambda args var e' -> Right $ Lambda args var (Upcast e')
    SPrim -> Left ApplyingNonProc

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
evaluateUntyped e (Upcast e') = evaluate e e'

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
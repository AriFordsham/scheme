{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Evaluate where

import Data.Kind (Type)
import Data.Map qualified as Map

import Scheme

evaluate :: Env -> ExprEx -> Either SchemeError ValueEx
evaluate e (ExprEx ex) = case ex of
  Var{} -> evaluate' e ex
  Value{} -> ValueEx <$> evaluate' e ex
  Call{} -> evaluate' e ex
  If{} -> evaluate' e ex
  CastProc{} -> ValueEx <$> evaluate' e ex

evaluate' :: Env -> Expr ty -> Either SchemeError (Evaluate' ty)
evaluate' e (Var s) =
  maybe (Left $ NotInScope s) Right (Map.lookup s e)
evaluate' _ (Value d) = Right d
evaluate' e (Call p args) = do
  p' <- evaluate' e p
  args' <- traverse (evaluate e) args
  case p' of
    Builtin f -> f args'
    Lambda args'' var body -> do
      e' <- zipArgs args'' args' var
      evaluate (e' <> e) body
evaluate' e (If tst t f) = do
  (ValueEx tst') <- evaluate e tst
  case tst' of
    Bool False -> case f of
      Nothing -> Left Undefined
      Just f' -> evaluate e f'
    _ -> evaluate e t
evaluate' e (CastProc ex) = do
  (ValueEx v) <- evaluate' e ex
  castProc v

zipArgs :: [String] -> [ValueEx] -> Maybe String -> Either SchemeError Env
zipArgs [] [] mv =
  Right $
    Map.empty
      <> maybe Map.empty (\v -> Map.singleton v (ValueEx $ list' [])) mv
zipArgs (s : ss) (a : as) v = Map.insert s a <$> zipArgs ss as v
zipArgs [] as (Just v) = Right $ Map.singleton v (ValueEx $ list' as)
zipArgs [] as Nothing = Left (WrongNumArgs "lambda" as)
zipArgs (_ : _) [] _ = Left (WrongNumArgs "lambda" [])

type family Evaluate' (ty :: Maybe SType) :: Type where
  Evaluate' 'Nothing = ValueEx
  Evaluate' ('Just ty) = Value ty 'Evaluate

castProc :: Value ty 'Evaluate -> Either SchemeError (Value 'Proc 'Evaluate)
castProc v = case valueToSing v of
  SProc -> Right v
  SPrim -> Left ApplyingNonProc

execute :: Value 'Prim 'Interpret -> Either SchemeError ValueEx
execute e = interpret e >>= evaluate (ValueEx . Builtin <$> procs)
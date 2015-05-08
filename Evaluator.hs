{-# LANGUAGE FlexibleInstances #-}
module Evaluator where

import BNFC.AbsLanguage
import Control.Monad.Reader hiding (sequence)
import Control.Monad.Trans.Either
import Data.Map (Map)
import qualified Data.Map as Map

data Value = VInt Integer
           | VBool Bool
           | VLam (Value -> EitherT String (Reader Env) Value) Env
           | VList [Value]

type Env = Map Ident Value
type IM = EitherT String (Reader Env)

instance Show Value where
  show (VInt x) = show x
  show (VBool x) = show x
  show (VLam _ _) = "lambda"
  show (VList xs) = show xs

class Evaluable a where
  eval :: a -> EitherT String (Reader Env) Value

instance Evaluable (Exp, Exp, Bool -> Bool -> Bool) where
  eval (e1, e2, f) = do
    VBool e1v <- eval e1
    VBool e2v <- eval e2
    return $ VBool (f e1v e2v)

instance (Evaluable (Exp, Exp, Integer -> Integer -> Bool)) where
  eval (e1, e2, f) = do
    VInt e1v <- eval e1
    VInt e2v <- eval e2
    return $ VBool (f e1v e2v)

instance Evaluable (Exp, Exp, Integer -> Integer -> Integer) where
  eval (e1, e2, f) = do
    VInt e1v <- eval e1
    VInt e2v <- eval e2
    return $ VInt (f e1v e2v)

instance Evaluable Param where
  eval (PInt i) = eval (EInt i)
  eval PBoolTrue = eval EBoolTrue
  eval PBoolFalse = eval EBoolFalse
  eval (PApp1 e) = eval (EApp1 e [])
  eval (PApp2 f) = eval (EApp2 f [])
  eval (PListConst1 es) = eval (EListConst1 es)

instance Evaluable Exp where
  -- Exp
  eval (ELet x params body e) = do
    fp <- mfix (\f -> local (Map.insert x f) (eval (ELam params body)))
    local (Map.insert x fp) (eval e)
  eval (EIf e1 e2 e3) = do
    VBool cond <- eval e1
    eval (if cond then e2 else e3)
  eval (ELam [] e) = eval e
  eval (ELam (param:params) e) = do
    env <- ask
    return $ VLam (\v -> local (Map.insert param v) (eval (ELam params e))) env
  eval (ENot e) = do 
    VBool b <- eval e
    return $ VBool (not b)
  -- Exp1
  eval (EAnd e1 e2)    = eval (e1, e2, (&&))
  eval (EOr e1 e2)     = eval (e1, e2, (||))
  eval (EEq e1 e2)     = eval (e1, e2, (==)  :: Integer -> Integer -> Bool)
  eval (ENeq e1 e2)    = eval (e1, e2, (/=)  :: Integer -> Integer -> Bool)
  eval (ELeq e1 e2)    = eval (e1, e2, (<=)  :: Integer -> Integer -> Bool)
  eval (EGeq e1 e2)    = eval (e1, e2, (>=)  :: Integer -> Integer -> Bool)
  eval (ELt e1 e2)     = eval (e1, e2, (<)   :: Integer -> Integer -> Bool)
  eval (EGt e1 e2)     = eval (e1, e2, (>)   :: Integer -> Integer -> Bool)
  -- Exp2
  eval (EPlus e1 e2)   = eval (e1, e2, (+)   :: Integer -> Integer -> Integer)
  eval (EMinus e1 e2)  = eval (e1, e2, (-)   :: Integer -> Integer -> Integer)
  -- Exp3
  eval (ETimes e1 e2)  = eval (e1, e2, (*)   :: Integer -> Integer -> Integer)
  eval (EObelus e1 e2) = eval (e1, e2, div   :: Integer -> Integer -> Integer)
  -- Exp4
  eval (EInt i) = return $ VInt i
  eval (ENInt i) = return $ VInt (-i)
  eval EBoolTrue = return $ VBool True 
  eval EBoolFalse = return $ VBool False
  eval (EApp1 e params) = do
    ev <- eval e
    foldM (\(VLam f env) param -> do
      paramv <- eval param
      local (const env) (f paramv)) ev params
  eval (EApp2 e params) = do
    ev <- asks (Map.! e)
    foldM (\(VLam f env) param -> do
      paramv <- eval param
      local (const env) (f paramv)) ev params
  eval (EListConst1 es) = do
    ese <- mapM eval es
    return $ VList ese
  eval (EListConst2 param params) = do
    paramv <- eval param
    VList paramsv <- eval params
    return $ VList (paramv:paramsv)

builtInFunctions :: [(Ident, Value)]
builtInFunctions = [
    (Ident "empty", VLam (\(VList l) -> return $ VBool (null l)) Map.empty),
    (Ident "head", VLam (\(VList xs) -> 
      if null xs then error "Empty list has no head." else return $ head xs) Map.empty),
    (Ident "tail", VLam (\(VList xs) ->
      if null xs then error "Empty list has no tail." else return $ VList (tail xs)) Map.empty)
  ]

runEval :: (Evaluable e) => e -> Either String Value
runEval e = runReader (runEitherT (eval e)) (Map.fromList builtInFunctions)

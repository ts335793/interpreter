module TypeInterference where

import BNFC.AbsLanguage
import Control.Applicative
import Control.Monad hiding (sequence)
import Control.Monad.Reader hiding (sequence)
import Control.Monad.Error hiding (sequence)
import Control.Monad.Trans.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Prelude ()
import Prelude.Compat

type Label = Int

infixr 5 :->
data Type = TInt
          | TBool
          | Type :-> Type
          | TVar Label
          | TList Type
  deriving (Eq, Show)

data QType = Forall (Set Label) Type
  deriving Show

data Env = Env (Map Ident QType)
  deriving Show

type IM = ErrorT String (StateT (Label, Map Label Type) (Reader Env))


class ContainingFreeVariables a where
  freeVariables :: a -> IM (Set Label)

freeVariables' :: Type -> IM (Set Label)
freeVariables' (TVar l) = return $ Set.singleton l
freeVariables' TInt = return Set.empty
freeVariables' TBool = return Set.empty
freeVariables' (t1 :-> t2) = do
  ft1 <- freeVariables' t1
  ft2 <- freeVariables' t2
  return $ ft1 <> ft2
freeVariables' (TList t) = freeVariables' t

instance ContainingFreeVariables Type where
  freeVariables t = do
    t' <- applySubstitutionsM t
    freeVariables' t'

instance ContainingFreeVariables QType where
  freeVariables (Forall vs t) = do 
    ft <- freeVariables t
    return $ ft Set.\\ vs

instance ContainingFreeVariables Env where
  freeVariables (Env env) =
    foldM (\acc qt -> do
      fqt <- freeVariables qt
      return $ acc <> fqt) Set.empty (Map.elems env)


newLabel :: IM Type
newLabel = do
  (x, y) <- lift get
  lift $ put (x + 1, y)
  return (TVar x)

getSubstitutions :: IM (Map Label Type)
getSubstitutions = do
  (_, y) <- lift get
  return y

setSubstitutions :: Map Label Type -> IM ()
setSubstitutions subs = do
  (x, _) <- lift get
  lift $ put (x, subs)

setSubstitution :: Label -> Type -> IM ()
setSubstitution l t = do
  subs <- getSubstitutions
  let subs' = Map.insert l t subs
      subs'' = Map.map (applySubstitutions subs') subs'
  setSubstitutions subs''

containsLabel :: Label -> Type -> IM Bool
containsLabel _ TInt = return False
containsLabel _ TBool = return False
containsLabel l (from :-> to) = (||) <$> containsLabel l from <*> containsLabel l to
containsLabel l (TVar x)
  | l == x = return True
  | otherwise = return False
containsLabel l (TList t) = containsLabel l t

applySubstitutions :: Map Label Type -> Type -> Type
applySubstitutions _ TInt = TInt
applySubstitutions _ TBool = TBool
applySubstitutions subs (from :-> to) = applySubstitutions subs from :-> applySubstitutions subs to
applySubstitutions subs (TVar x) = fromMaybe (TVar x) (Map.lookup x subs)
applySubstitutions subs (TList t) = TList (applySubstitutions subs t)

applySubstitutionsM :: Type -> IM Type
applySubstitutionsM t = do
  subs <- getSubstitutions
  return $ applySubstitutions subs t

unificate' :: Type -> Type -> IM ()
unificate' TInt TInt = return ()
unificate' TBool TBool = return ()
unificate' (fromL :-> toL) (fromR :-> toR) = do
  unificate' fromL fromR
  toL' <- applySubstitutionsM toL
  toR' <- applySubstitutionsM toR
  unificate' toL' toR'
unificate' (TVar l) (TVar r)
  | l == r = return ()
  | otherwise = setSubstitution l (TVar r)
unificate' (TVar l) rt = do
  cond <- containsLabel l rt
  if cond
    then throwError "Found recursive type."
    else setSubstitution l rt
unificate' lt (TVar r) = unificate' (TVar r) lt
unificate' (TList lt) (TList rt) = unificate' lt rt
unificate' l r = throwError $ "Couldnt unificate type " ++ show l ++ " with " ++ show r ++ "."

unificate :: Type -> Type -> IM ()
unificate t1 t2 = do
  et1 <- applySubstitutionsM t1
  et2 <- applySubstitutionsM t2
  unificate' et1 et2

generalize :: Type -> IM QType
generalize t = do
  e <- ask
  tfv <- freeVariables t
  efv <- freeVariables e
  return $ Forall (tfv Set.\\ efv) t

instantiate :: QType -> IM Type
instantiate (Forall vs t) = do
  t' <- applySubstitutionsM t
  subs <- sequence $ Map.fromSet (const newLabel) vs
  return $ applySubstitutions subs t'

class Typeable a where
  typeOf :: a -> IM Type

instance Typeable Param where
  typeOf (PInt x) = typeOf (EInt x)
  typeOf PBoolTrue = typeOf EBoolTrue
  typeOf PBoolFalse = typeOf EBoolFalse
  typeOf (PApp1 e) = typeOf (EApp1 e [])
  typeOf (PApp2 e) = typeOf (EApp2 e [])
  typeOf (PListConst1 l) = typeOf (EListConst1 l)

emptyQType :: Type -> QType
emptyQType t = Forall Set.empty t

envInsert :: Ident -> QType -> Env -> Env
envInsert x qt (Env e) = Env (Map.insert x qt e)

envGet :: Ident -> IM QType
envGet i = do
  Env env <- ask
  case Map.lookup i env of
    Just qt -> return qt
    Nothing -> throwError $ "Unknown identyfier " ++ show i ++ "."

typeOfBB e = do
  et <- typeOf e
  unificate et TBool
  return TBool
typeOfABC a b c e1 e2 = do
  e1t <- typeOf e1
  e2t <- typeOf e2
  unificate e1t a
  unificate e2t b
  return c
typeOfBBB e1 e2 = typeOfABC TBool TBool TBool e1 e2
typeOfIIB e1 e2 = typeOfABC TInt TInt TBool e1 e2
typeOfIII e1 e2 = typeOfABC TInt TInt TInt e1 e2

typeOfApplyArgumentsToFunction :: Type -> [Param] -> IM Type
typeOfApplyArgumentsToFunction ft params =
  foldM (\acc param -> do
    paramt <- typeOf param
    ot <- newLabel
    unificate acc (paramt :-> ot)
    return ot) ft params


instance Typeable Exp where
  -- Exp
  typeOf (ELet x params body e) = do
    xt <- newLabel
    bodyt <- local (envInsert x (emptyQType xt)) (typeOf (ELam params body))
    unificate xt bodyt
    gxt <- generalize xt
    local (envInsert x gxt) (typeOf e)
  typeOf (EIf e1 e2 e3) = do
    e1t <- typeOf e1
    e2t <- typeOf e2
    e3t <- typeOf e3
    unificate e1t TBool
    unificate e2t e3t
    return e2t
  typeOf (ELam [] e) = typeOf e
  typeOf (ELam (param:params) e) = do
    paramt <- newLabel
    et <- local (envInsert param (emptyQType paramt)) (typeOf (ELam params e))
    applySubstitutionsM (paramt :-> et)
  -- Exp1
  typeOf (ENot e) = typeOfBB e
  typeOf (EAnd e1 e2) = typeOfBBB e1 e2
  typeOf (EOr e1 e2) = typeOfBBB e1 e2
  typeOf (EEq e1 e2) = typeOfIIB e1 e2
  typeOf (ENeq e1 e2) = typeOfIIB e1 e2
  typeOf (ELeq e1 e2) = typeOfIIB e1 e2
  typeOf (EGeq e1 e2) = typeOfIIB e1 e2
  typeOf (ELt e1 e2) = typeOfIIB e1 e2
  typeOf (EGt e1 e2) = typeOfIIB e1 e2
  -- Exp2
  typeOf (EPlus e1 e2) = typeOfIII e1 e2
  typeOf (EMinus e1 e2) = typeOfIII e1 e2
  -- Exp3
  typeOf (ETimes e1 e2) = typeOfIII e1 e2
  typeOf (EObelus e1 e2) = typeOfIII e1 e2
  -- Exp4
  typeOf (EInt _) = return TInt
  typeOf (ENInt _) = return TInt
  typeOf EBoolTrue = return TBool
  typeOf EBoolFalse = return TBool
  typeOf (EApp1 f params) = do
    ft <- typeOf f
    typeOfApplyArgumentsToFunction ft params
  typeOf (EApp2 f params) = do
    fqt <- envGet f
    ft <- instantiate fqt
    typeOfApplyArgumentsToFunction ft params
  typeOf (EListConst1 elems) = do
    t <- newLabel
    foldM (\acc elem -> do
      elemt <- typeOf elem
      unificate acc (TList elemt)
      return acc) (TList t) elems
  typeOf (EListConst2 p1 p2) = do
    p1t <- typeOf p1
    p2t <- typeOf p2
    t <- newLabel
    unificate p2t (TList t)
    unificate (TList p1t) p2t
    return (TList p1t)


builtInFunctions :: [(Ident, QType)]
builtInFunctions = [
    (Ident "empty", Forall (Set.singleton (-1)) (TList (TVar (-1)) :-> TBool)),
    (Ident "head", Forall (Set.singleton (-2)) (TList (TVar (-2)) :-> TVar (-2))),
    (Ident "tail", Forall (Set.singleton (-3)) (TList (TVar (-3)) :-> TList (TVar (-3))))
  ]

runTypeOf :: Exp -> Either String Type
runTypeOf e = 
  case runReader (runStateT (runErrorT (typeOf e)) (0, Map.empty)) (Env (Map.fromList builtInFunctions)) of
    (Left msg, (_, _)) -> Left msg
    (Right t, (_, subs)) -> return $ applySubstitutions subs t

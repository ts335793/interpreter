module TypeInterference where

import BNFC.AbsLanguage
import Control.Applicative
import Control.Monad hiding (sequence)
import Control.Monad.Reader hiding (sequence)
import Control.Monad.Trans.Either
import Control.Monad.Trans.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Prelude ()
import Prelude.Compat

-- import Debug.Trace

-- traceM :: (Monad m) => String -> m ()
-- traceM string = trace string $ return ()

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

type IM = EitherT String (StateT (Label, Map Label Type) (Reader Env))


class ContainingFreeVariables a where
  freeVariables :: a -> IM (Set Label)

freeVariables' (TVar l) = return $ Set.singleton l
freeVariables' TInt = return $ Set.empty
freeVariables' TBool = return $ Set.empty
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
  freeVariables (Env env) = do
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
setSubstitution l t
  | TVar l == t = return ()
  | otherwise = do
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

applySubstitutions :: (Map Label Type) -> Type -> Type
applySubstitutions subs TInt = TInt
applySubstitutions subs TBool = TBool
applySubstitutions subs (from :-> to) = ((applySubstitutions subs from) :-> (applySubstitutions subs to))
applySubstitutions subs (TVar x) =
  case Map.lookup x subs of
    Just xs -> xs
    Nothing -> TVar x
applySubstitutions subs (TList t) = TList (applySubstitutions subs t)

applySubstitutionsM :: Type -> IM Type
applySubstitutionsM t = do
  subs <- getSubstitutions
  return $ applySubstitutions subs t

unificate' :: Type -> Type -> IM Type
unificate' TInt TInt = return TInt
unificate' TBool TBool = return TBool
unificate' (fromL :-> toL) (fromR :-> toR) = do
  fromU <- unificate' fromL fromR
  toL' <- applySubstitutionsM toL
  toR' <- applySubstitutionsM toR
  toU <- unificate' toL' toR'
  return $ fromU :-> toU
unificate' (TVar l) rt = do
  cond <- containsLabel l rt
  if cond
    then error $ "Found recursive type."
    else do
      setSubstitution l rt
      return rt
unificate' lt (TVar r) = do
  cond <- containsLabel r lt
  if cond
    then error $ "Found recursive type."
    else do
      setSubstitution r lt
      return lt
unificate' (TList lt) (TList rt) = do
  ut <- unificate' lt rt
  return (TList ut)
unificate' l r = error $ "Couldnt unificate type " ++ (show l) ++ " with " ++ (show r) ++ "."

unificate :: Type -> Type -> IM Type
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
  -- env <- ask
  -- subs <- getSubstitutions
  -- traceM ("INST0: " ++ show env ++ " " ++ show subs)
  -- traceM ("INST1: " ++ show vs ++ " " ++ show t)
  t' <- applySubstitutionsM t
  subs <- sequence $ Map.fromSet (const newLabel) vs
  return $ applySubstitutions subs t'

class Typeable a where
  typeOf :: a -> IM Type

instance Typeable Param where
  typeOf (PInt x) = typeOf (EInt x)
  typeOf (PApp1 e) = typeOf (EApp1 e [])
  typeOf (PApp2 e) = typeOf (EApp2 e [])
  typeOf (PListConst1 l) = typeOf (EListConst1 l)

emptyQType :: Type -> QType
emptyQType t = Forall Set.empty t

envInsert :: Ident -> QType -> Env -> Env
envInsert x qt (Env e) = Env (Map.insert x qt e)

envGet :: Ident -> Env -> QType
envGet i (Env e) = e Map.! i

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

-- -> rozw
instance Typeable Exp where
  -- Exp
  typeOf (ELet x params body e) = do
    xt <- newLabel
    -- env <- ask
    -- subs <- getSubstitutions
    -- traceM ("ELET0: " ++ show env ++ " | " ++ show subs)
    -- traceM ("ELET0.1: " ++ show e)
    -- traceM ("ELET1: " ++ show xt)
    bodyt <- local (envInsert x (emptyQType xt)) (typeOf (ELam params body))
    -- subs <- getSubstitutions
    -- traceM ("ELET2: " ++ show bodyt ++ " |  " ++ show subs)
    unificate xt bodyt
    gxt <- generalize xt
    -- subs <- getSubstitutions
    -- traceM ("ELET3: " ++ show gxt ++ " | " ++ show subs)
    local (envInsert x gxt) (typeOf e)
  typeOf (EIf e1 e2 e3) = do
    e1t <- typeOf e1
    e2t <- typeOf e2
    e3t <- typeOf e3
    unificate e1t TBool
    unificate e2t e3t
  typeOf (ELam [] e) = -- do
    -- env <- ask
    -- subs <- getSubstitutions
    -- traceM ("ELAM[]0: " ++ show env ++ " " ++ show subs)
    -- traceM ("ELAM[]1: " ++ show e)
    typeOf e
  typeOf (ELam (param:params) e) = do
    paramt <- newLabel
    -- env <- ask
    -- subs <- getSubstitutions    
    -- traceM ("ELAM[..]0: " ++ show env ++ " " ++ show subs)
    -- traceM ("ELAM[..]1: " ++ show e)
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
  typeOf (EApp1 f params) = do
    ft <- typeOf f
    foldM (\acc param -> do
      paramt <- typeOf param
      ot <- newLabel
      unificate acc (paramt :-> ot)
      return ot) ft params
  typeOf (EApp2 f params) = do
    fqt <- asks (envGet f)
    -- subs <- getSubstitutions
    -- env <- ask
    -- traceM ("EAPP[]0: " ++ show env ++ " " ++ show subs)
    -- traceM ("EAPP[]1: " ++ show f ++ " " ++ show params)
    ft <- instantiate fqt
    -- traceM ("EAPP[]2: " ++ show ft)
    foldM (\acc param -> do
      paramt <- typeOf param
      ot <- newLabel
      unificate acc (paramt :-> ot)
      return ot) ft params
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

runTypeOf :: Exp -> Either String Type
runTypeOf e = 
  case runReader (runStateT (runEitherT (typeOf e)) (0, Map.empty)) (Env Map.empty) of
    (Left msg, (l, subs)) -> error msg
    (Right t, (l, subs)) -> return $ applySubstitutions subs t

checkType2 e = 
  case runReader (runStateT (runEitherT (typeOf e)) (0, Map.empty)) (Env Map.empty) of
    (Left msg, (l, subs)) -> error msg
    (Right t, (l, subs)) -> (t, l, subs, applySubstitutions subs t)

test1 = ELam [Ident "x"] (EApp2 (Ident "x") [])
test2 = ELam [Ident "x", Ident "y"] (EApp2 (Ident "x") [])
test3 = ELam [Ident "x", Ident "y", Ident "z"] (
  EApp1 (EApp2 (Ident "x") [PApp2 (Ident "z")])
    [PApp1 (EApp2 (Ident "y") [PApp2 (Ident "z")])])

intList = EListConst1 [EInt 1]
list = EListConst1 []
test4 = ELam [Ident "x"] (EIf (EApp2 (Ident "x") [PInt 1]) list intList)
test5 = ELet (Ident "id") [(Ident "x")] (EApp2 (Ident "x") []) (EApp2 (Ident "id") [PApp2 (Ident "id"), PInt 6]) -- let id x = x in id id 5
test5_1 = ELet (Ident "id") [(Ident "x")] (EApp2 (Ident "x") []) (EApp2 (Ident "id") [PApp2 (Ident "id")]) -- let id x = x in id id

-- let id x = x in id
test6 = ELet (Ident "id") [(Ident "x")] (EApp2 (Ident "x") []) (EApp2 (Ident "id") [])
-- (\id -> id id 5) (x x) // fail
test7 = EApp1 (ELam [Ident "id"] (EApp2 (Ident "id") [PApp2 (Ident "id"), PInt 5]))
              [PApp1 (ELam [Ident "x"] (EApp2 (Ident "x") []))]
-- (\id -> id id 5) // fail
test8 = ELam [Ident "id"] (EApp2 (Ident "id") [PApp2 (Ident "id"), PInt 5])
-- (\id -> id 5)
test9 = ELam [Ident "id"] (EApp2 (Ident "id") [PInt 5])

module TypeInterference where

import BNFC.AbsLanguage
import Control.Monad.Reader
import Control.Monad.Trans.Either
import Control.Monad.Trans.State
import Data.Map hiding (foldr)
import Prelude hiding (lookup)

type Label = Int

infixr 5 :->
data Type = TInt
          | TBool
          | Type :-> Type
          | TVar Label
          | TList (Maybe Type)
  deriving (Eq, Show)

type IM = EitherT String (StateT (Int, Map Label Type) (Reader (Map Ident Type)))

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

getMaybeSubstitution :: Label -> IM (Maybe Type)
getMaybeSubstitution l = do
  subs <- getSubstitutions
  return $ lookup l subs

hasSubstitution :: Label -> IM Bool
hasSubstitution l = do
  subs <- getSubstitutions
  return $ member l subs

setSubstitution :: Label -> Type -> IM ()
setSubstitution l t = do
  subs <- getSubstitutions
  setSubstitutions (insert l t subs)

getSubstitution :: Label -> IM Type
getSubstitution l = do
  subs <- getSubstitutions
  return $ subs ! l

containsLabel :: Label -> Type -> IM Bool
containsLabel _ TInt = return False
containsLabel _ TBool = return False
containsLabel l (from :-> to) = liftM2 (||) (containsLabel l from) (containsLabel l to)
containsLabel l (TVar x) =
  if x == l then
    return True
  else do
    mxt <- getMaybeSubstitution x
    case mxt of
      Just xt -> containsLabel l xt
      Nothing -> return False
containsLabel l (TList mt) =
  case mt of
    Just t -> containsLabel l t
    Nothing -> return False

unificate :: Type -> Type -> IM ()
unificate TInt TInt = return ()
unificate TBool TBool = return ()
unificate (fromL :-> toL) (fromR :-> toR) = unificate fromL fromR >> unificate toL toR
unificate lt@(TVar l) rt@(TVar r) = do
  ml <- hasSubstitution l
  mr <- hasSubstitution r
  if not ml then do
    cond <- containsLabel l rt
    if cond then error "Recursive type." else setSubstitution l rt
  else if not mr then do
    cond <- containsLabel r lt
    if cond then error "Recursive type." else setSubstitution r lt
  else do
    lt' <- getSubstitution l
    rt' <- getSubstitution r
    unificate lt' rt'
unificate lt@(TVar l) rt = do
  mlt <- getMaybeSubstitution l
  case mlt of
    Just lt' -> unificate lt' rt
    Nothing -> setSubstitution l rt
unificate lt rt@(TVar _) = unificate rt lt
unificate (TList mlt) (TList mrt) = do
  case (mlt, mrt) of
    (Just lt, Just rt) -> unificate lt rt
    otherwise -> return ()
unificate l r = error $ "Couldnt unificate type " ++ (show l) ++ " with " ++ (show r) ++ "."

typeOf'BB e = do
  et <- typeOf' e
  unificate et TBool
  return TBool
typeOf'abc a b c e1 e2 = do
  e1t <- typeOf' e1
  e2t <- typeOf' e2
  unificate e1t a
  unificate e2t b
  return c
typeOf'BBB e1 e2 = typeOf'abc TBool TBool TBool e1 e2
typeOf'IIB e1 e2 = typeOf'abc TInt TInt TBool e1 e2
typeOf'III e1 e2 = typeOf'abc TInt TInt TInt e1 e2

typeOfParam' :: Param -> IM Type
typeOfParam' (PInt x) = typeOf' (EInt x)
typeOfParam' (PApp1 e) = typeOf' (EApp1 e [])
typeOfParam' (PApp2 e) = typeOf' (EApp2 e [])
typeOfParam' (PListConst1 l) = typeOf' (EListConst1 l)

typeOf' :: Exp -> IM Type
-- Exp
typeOf' (ELet x params body e) = do
  xt <- newLabel
  bodyt <- local (insert x xt) (typeOf' (ELam params body))
  unificate xt bodyt
  local (insert x xt) (typeOf' e)
typeOf' (EIf e1 e2 e3) = do
  e1t <- typeOf' e1
  e2t <- typeOf' e2
  e3t <- typeOf' e3
  unificate e1t TBool
  unificate e2t e3t
  return e2t
typeOf' (ELam [] e) = typeOf' e
typeOf' (ELam (param:params) e) = do
  paramt <- newLabel
  local (insert param paramt) (typeOf' (ELam params e))
-- Exp1
typeOf' (ENot e) = typeOf'BB e
typeOf' (EAnd e1 e2) = typeOf'BBB e1 e2
typeOf' (EOr e1 e2) = typeOf'BBB e1 e2
typeOf' (EEq e1 e2) = typeOf'IIB e1 e2
typeOf' (ENeq e1 e2) = typeOf'IIB e1 e2
typeOf' (ELeq e1 e2) = typeOf'IIB e1 e2
typeOf' (EGeq e1 e2) = typeOf'IIB e1 e2
typeOf' (ELt e1 e2) = typeOf'IIB e1 e2
typeOf' (EGt e1 e2) = typeOf'IIB e1 e2
-- Exp2
typeOf' (EPlus e1 e2) = typeOf'III e1 e2
typeOf' (EMinus e1 e2) = typeOf'III e1 e2
-- Exp3
typeOf' (ETimes e1 e2) = typeOf'III e1 e2
typeOf' (EObelus e1 e2) = typeOf'III e1 e2
-- Exp4
typeOf' (EInt _) = return TInt
typeOf' (EApp1 f []) = typeOf' f
typeOf' (EApp1 f (param:params)) = do
  ft <- typeOf' (EApp1 f params)
  paramt <- typeOfParam' param
  ot <- newLabel
  unificate ft (paramt :-> ot)
  return ot
typeOf' (EApp2 f []) = asks (! f)
typeOf' (EApp2 f (param:params)) = do
  ft <- typeOf' (EApp2 f params)
  paramt <- typeOfParam' param
  ot <- newLabel
  unificate ft (paramt :-> ot)
  return ot
typeOf' (EListConst1 elems) =
  foldM (\acc elem -> do
    elemt <- typeOf' elem
    unificate acc elemt
    return $ TList (Just elemt)) (TList Nothing) elems
typeOf' (EListConst2 p1 p2) = do
  p1t <- typeOfParam' p1
  p2t <- typeOfParam' p2
  case p2t of
    TList Nothing -> return $ TList (Just p1t)
    TList (Just p2et) -> do
      unificate p1t p2et
      return p2et
    otherwise -> error $ "Cannot construct list from types: " ++ show p1t ++ ", " ++ show p2t ++ "."

applySubstitutions :: Type -> IM Type
applySubstitutions TInt = return TInt
applySubstitutions TBool = return TBool
applySubstitutions (from :-> to) = liftM2 (:->) (applySubstitutions from) (applySubstitutions to)
applySubstitutions xt@(TVar x) = do
  mxt <- getMaybeSubstitution x
  case mxt of
    Just xt' -> applySubstitutions xt'
    Nothing -> return xt
applySubstitutions (TList Nothing) = return (TList Nothing)
applySubstitutions (TList (Just t)) = do
  t' <- applySubstitutions t
  return (TList (Just t'))

typeOf :: Exp -> Type
typeOf e = 
  case runReader (runStateT (runEitherT (typeOf' e)) (0, empty)) empty of
    (Left msg, (l, subs)) -> error msg
    (Right t, (l, subs)) -> 
      let (Right t', _) = runReader (runStateT (runEitherT (applySubstitutions t)) (l, subs)) empty
      in t'

module TypeInterference where

import BNFC.AbsLanguage
import Control.Monad.Reader hiding (sequence)
import Control.Monad.Trans.Either
import Control.Monad.Trans.State
import Data.Map hiding (foldr)
import Data.Set (Set)
import Control.Applicative hiding (empty)
import qualified Data.Set as Set
import Prelude.Compat hiding (lookup)
import Data.Monoid ((<>))
import Prelude ()
import Debug.Trace

type Label = Int

infixr 5 :->
data Type = TInt
          | TBool
          | Type :-> Type
          | TVar Label
          | TList Type
  deriving (Eq, Show)

data QType = Forall (Set Label) Type

type IM = EitherT String (StateT (Label, Map Label Type) (Reader (Map Ident QType)))

traceM :: (Monad m) => String -> m ()
traceM string = trace string $ return ()

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
containsLabel l (TVar x) = do
  if x == l then
    return True
  else do
    mxt <- getMaybeSubstitution x
    case mxt of
      Just xt -> containsLabel l xt
      Nothing -> return False
containsLabel l (TList t) = containsLabel l t

checkCycles :: IM ()
checkCycles = do
  subs <- getSubstitutions
  mapWithKey (\l sub -> containsLabel l sub) subs

unificate :: Type -> Type -> IM ()
unificate TInt TInt = do
  traceM "sddd"
  return ()
unificate TBool TBool = do
  traceM "----><><M"
  return ()
unificate (fromL :-> toL) (fromR :-> toR) = do
  traceM "dsafasdfsf"
  unificate fromL fromR
  unificate toL toR
unificate lt@(TVar l) rt@(TVar r) = do
  traceM "dfasdfasdf"
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
  traceM "1111111"
  mlt <- getMaybeSubstitution l
  case mlt of
    Just lt' -> unificate lt' rt
    Nothing -> setSubstitution l rt
unificate lt rt@(TVar _) = do
  traceM "asaaaaaa"
  unificate rt lt
unificate (TList lt) (TList rt) = do
  traceM "dfasdfaf"
  unificate lt rt
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

typeFreeVars :: Type -> IM (Set Label)
typeFreeVars (TVar l)    = do
  s <- getMaybeSubstitution l
  case s of    
    Nothing -> return (Set.singleton l)
    Just t -> typeFreeVars t
typeFreeVars TInt = return Set.empty
typeFreeVars TBool = return Set.empty
typeFreeVars (t1 :-> t2) = do
  l1 <- typeFreeVars t1
  l2 <- typeFreeVars t2
  return (l1 <> l2)
typeFreeVars (TList t) = typeFreeVars t

envFreeVars :: IM (Set Label)
envFreeVars = do
  env <- ask :: IM (Map Ident QType)
  foldM (\acc (Forall vars t) -> do
    fvars <- typeFreeVars t :: IM (Set Label)
    return $ acc <> (fvars Set.\\ vars)) Set.empty (elems env)

generalize :: Type -> IM QType
generalize t = do
  tfv <- typeFreeVars t
  efv <- envFreeVars
  return (Forall (tfv Set.\\ efv) t)

instantiate :: QType -> IM Type
instantiate (Forall v t) = do
    traceM "l-l"
    labels <- sequence $ fromSet (const newLabel) v
    let go' x = traceM "go'" >> go x
        go (TVar l)  
          | Set.member l v = return (labels ! l)
          | otherwise = do
            mt' <- getMaybeSubstitution l
            case mt' of
              Nothing -> return (TVar l)
              Just t' -> go' t'
        go (TList t') = TList <$> go' t'
        go (t1 :-> t2) = (:->) <$> go' t1 <*> go' t2
        go x = return x
    go' t     

typeOf' :: Exp -> IM Type
-- Exp
typeOf' (ELet x params body e) = do
  xt <- newLabel
  bodyt <- local (insert x (Forall Set.empty xt)) (typeOf' (ELam params body))
  unificate xt bodyt
  gxt <- generalize xt
  local (insert x gxt) (typeOf' e)
typeOf' (EIf e1 e2 e3) = do
  e1t <- typeOf' e1
  e2t <- typeOf' e2
  e3t <- typeOf' e3
  unificate e1t TBool
  unificate e2t e3t
  return e2t
typeOf' (ELam [] e) = do
  traceM "fff"
  typeOf' e
typeOf' (ELam (param:params) e) = do
  traceM "ooo"
  paramt <- newLabel
  et <- local (insert param (Forall Set.empty paramt)) (typeOf' (ELam params e))
  return (paramt :-> et)
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
typeOf' (EApp1 f params) = do
  ft <- typeOf' f
  foldM (\acc param -> do
    paramt <- typeOfParam' param
    ot <- newLabel
    unificate acc (paramt :-> ot)
    return ot) ft params
typeOf' (EApp2 f params) = do
  traceM "dupa"
  fqt <- asks (! f)
  ft <- instantiate fqt
  foldM (\acc param -> do
    traceM "asd"
    paramt <- typeOfParam' param
    ot <- newLabel
    unificate acc (paramt :-> ot)
    return ot) ft params
typeOf' (EListConst1 elems) = do
  t <- newLabel
  foldM (\acc elem -> do
    elemt <- typeOf' elem
    unificate acc (TList elemt)
    return acc) (TList t) elems
typeOf' (EListConst2 p1 p2) = do
  p1t <- typeOfParam' p1
  p2t <- typeOfParam' p2
  t <- newLabel
  unificate p2t (TList t)
  unificate (TList p1t) p2t
  return (TList p1t)

applySubstitutions :: Type -> IM Type
applySubstitutions TInt = return TInt
applySubstitutions TBool = return TBool
applySubstitutions (from :-> to) = liftM2 (:->) (applySubstitutions from) (applySubstitutions to)
applySubstitutions xt@(TVar x) = do
  traceM "liisdl"
  mxt <- getMaybeSubstitution x
  case mxt of
    Just xt' -> applySubstitutions xt'
    Nothing -> return xt
applySubstitutions (TList t) = do
  traceM "DSsdF"
  t' <- applySubstitutions t
  return (TList t')

typeOf :: Exp -> Type
typeOf e = 
  case runReader (runStateT (runEitherT (typeOf' e)) (0, empty)) empty of
    (Left msg, (l, subs)) -> error msg
    (Right t, (l, subs)) -> 
      let (Right t', _) = runReader (runStateT (runEitherT (applySubstitutions t)) (l, subs)) empty
      in t'
typeOf2 e = 
  case runReader (runStateT (runEitherT (typeOf' e)) (0, empty)) empty of
    (Left msg, (l, subs)) -> error msg
    (Right t, (l, subs)) -> 
      let (Right t', _) = runReader (runStateT (runEitherT (applySubstitutions t)) (l, subs)) empty
      in (t, l, subs, t')

test1 = ELam [Ident "x"] (EApp2 (Ident "x") [])
test2 = ELam [Ident "x", Ident "y"] (EApp2 (Ident "x") [])
test3 = ELam [Ident "x", Ident "y", Ident "z"] (
  EApp1 (EApp2 (Ident "x") [PApp2 (Ident "z")])
    [PApp1 (EApp2 (Ident "y") [PApp2 (Ident "z")])])

intList = EListConst1 [EInt 1]
list = EListConst1 []
test4 = ELam [Ident "x"] (EIf (EApp2 (Ident "x") [PInt 1]) list intList)
test5 = ELet (Ident "id") [(Ident "x")] (EApp2 (Ident "x") []) (EApp2 (Ident "id") [PApp2 (Ident "id"), PInt 5])
test6 = ELet (Ident "id") [(Ident "x")] (EApp2 (Ident "x") []) (EApp2 (Ident "id") [])
test7 = EApp1 (ELam [Ident "id"] (EApp2 (Ident "id") [PApp2 (Ident "id"), PInt 5]))
              [PApp1 (ELam [Ident "x"] (EApp2 (Ident "x") []))]
test8 = ELam [Ident "id"] (EApp2 (Ident "id") [PApp2 (Ident "id"), PInt 5])
test9 = ELam [Ident "id"] (EApp2 (Ident "id") [PInt 5])
-- s = let id x = x in (id id) 2
-- \id -> id id 5

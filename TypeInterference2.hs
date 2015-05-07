module TypeInterference2 where

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

type Label = Int

infixr 5 :->
data Type = TInt
          | TBool
          | Type :-> Type
          | TVar Label
          | TList Type
  deriving (Eq, Show)

data QType = Forall (Set Label) Type

data Env = Env (Map Ident QType)

type IM = EitherT String (StateT (Label, Map Label Type) (Reader (Map Ident QType)))

class ContainingFreeVariables a where
  freeVariables :: a -> Set Label

instance ContainingFreeVariables Type where
  freeVariables (TVar l) = Set.singleton l
  freeVariables TInt = Set.empty
  freeVariables TBool = Set.empty
  freeVariables (t1 :-> t2) = freeVariables t1 <> freeVariables t2
  freeVariables (TList t) = freeVariables t

instance ContainingFreeVariables QType where
  freeVariables (Forall vs t) = (freeVariables t) Set.\\ vs

instance ContainingFreeVariables Env where
  freeVariables (Env env) = foldr (\qt acc -> acc <> (freeVariables qt)) Set.empty (Map.elems env)

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

applySubstitutions :: (Map Label Type) -> Type -> Type
applySubstitutions subs TInt = TInt
applySubstitutions subs TBool = TBool
applySubstitutions subs (from :-> to) = ((applySubstitutions subs from) :-> (applySubstitutions subs to))
applySubstitutions subs (TVar x) =
  case Map.lookup x subs of
    Just xs -> applySubstitutions subs xs
    Nothing -> TVar x
applySubstitutions subs (TList t) = TList $ applySubstitutions subs t

applySubstitutionsM :: Type -> IM Type
applySubstitutionsM t = do
  subs <- getSubstitutions
  return $ applySubstitutions subs t

unificate :: Type -> Type -> IM Type
unificate TInt TInt = return TInt
unificate TBool TBool = return TBool
unificate (fromL :-> toL) (fromR :-> toR) = do
  fromU <- unificate fromL fromR
  toL' <- applySubstitutionsM toL
  toR' <- applySubstitutionsM toR
  toU <- unificate toL' toR'
  return $ fromU :-> toU
unificate (TVar l) rt = do
  cond <- containsLabel l rt
  if cond
    then error $ "Found recursive type."
    else do
      setSubstitution l rt
      return rt
unificate lt (TVar r) = do
  cond <- containsLabel r lt
  if cond
    then error $ "Found recursive type."
    else do
      setSubstitution r lt
      return lt
unificate (TList lt) (TList rt) = do
  ut <- unificate lt rt
  return (TList ut)
unificate l r = error $ "Couldnt unificate type " ++ (show l) ++ " with " ++ (show r) ++ "."

{-generalize :: Type -> IM QType
generalize t = do
  tfv <- typeFreeVariables t
  efv <- envFreeVariables
  return $ Forall (tfv Set.\\ efv) t

instantiate :: QType -> IM Type
instantiate (Forall vs t) = do
  subs <- sequence $ Map.fromSet (const newLabel) vs
  return $ applySubstitutions subs t-}

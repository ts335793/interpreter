module TypeInterference where

import BNFC.AbsLanguage
import Prelude hiding (lookup)
import Control.Monad.Reader
import Control.Monad.Trans.Either
import Control.Monad.Trans.State

type Label = Int

infixr 5 :->
data Type = TInt
          | TBool
          | Type :-> Type
          | TVar Label
          | TList (Maybe Type)
  deriving (Eq, Show)


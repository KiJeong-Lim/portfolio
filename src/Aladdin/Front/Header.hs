module Aladdin.Front.Header where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

type ErrMsg = String

type SPos = (Int, Int)

type LargeId = String

type SmallId = String

type Keyword = String

data SLoc
    = SLoc
        { _BegPos :: SPos
        , _EndPos :: SPos
        }
    deriving (Eq, Ord)

newtype Unique
    = Unique { unUnique :: Integer }
    deriving (Eq, Ord)

newtype UniqueGenT m a
    = UniqueGenT { unUniqueGenT :: StateT Integer m a }
    deriving ()

data Literal
    = NatL Integer
    | ChrL Char
    | StrL String
    deriving (Eq, Ord)

data Fixity
    = Prefix
    | InfixL
    | InfixR
    | InfixN
    deriving (Eq, Ord)

data LogicalOperator
    = LO_ty_pi
    | LO_if
    | LO_true
    | LO_fail
    | LO_cut
    | LO_and
    | LO_or
    | LO_imply
    | LO_pi
    | LO_sigma
    deriving (Eq, Ord, Show)

data DataConstructor
    = DC_LO LogicalOperator
    | DC_Named SmallId
    | DC_Unique Unique
    | DC_Nil
    | DC_Cons
    | DC_ChrL Char
    | DC_NatL Integer
    | DC_Succ
    deriving (Eq, Ord, Show)

data TypeConstructor
    = TC_Arrow
    | TC_Named SmallId
    | TC_Unique Unique
    deriving (Eq, Ord, Show)

data Constant
    = DC DataConstructor
    | TC TypeConstructor
    deriving (Eq, Ord, Show)

class HasSLoc a where
    getSLoc :: a -> SLoc

class HasAnnot f where
    getAnnot :: f a -> a
    putAnnot :: a -> f a -> f a

class Monad m => GenUniqueM m where
    getNewUnique :: m Unique

instance Semigroup SLoc where
    SLoc pos1 pos2 <> SLoc pos1' pos2' = SLoc (min pos1 pos1') (max pos2 pos2')

instance Show SLoc where
    showsPrec _ = const id

instance Show Unique where
    showsPrec _ = showsPrec 0 . unUnique

instance Functor m => Functor (UniqueGenT m) where
    fmap a2b = UniqueGenT . fmap a2b . unUniqueGenT

instance Monad m => Applicative (UniqueGenT m) where
    pure = UniqueGenT . pure
    m1 <*> m2 = UniqueGenT (unUniqueGenT m1 <*> unUniqueGenT m2)

instance Monad m => Monad (UniqueGenT m) where
    m1 >>= m2 = UniqueGenT (unUniqueGenT m1 >>= unUniqueGenT . m2)

instance Monad m => GenUniqueM (UniqueGenT m) where
    getNewUnique = UniqueGenT go where
        go :: Monad m => StateT Integer m Unique
        go = do
            n <- get
            let n' = n + 1
            n' `seq` put n'
            return (Unique n')

instance MonadTrans UniqueGenT where
    lift = UniqueGenT . lift

instance MonadIO m => MonadIO (UniqueGenT m) where
    liftIO = UniqueGenT . liftIO

runUniqueGenT :: Functor m => UniqueGenT m a -> m a
runUniqueGenT = fmap fst . flip runStateT 0 . unUniqueGenT

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

type MetaTVar = Unique

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
    deriving (Eq, Ord)

data DataConstructor
    = DC_LO LogicalOperator
    | DC_Named SmallId
    | DC_Unique Unique
    | DC_Nil
    | DC_Cons
    | DC_ChrL Char
    | DC_NatL Integer
    | DC_Succ
    deriving (Eq, Ord)

data TypeConstructor
    = TC_Arrow
    | TC_Named SmallId
    | TC_Unique Unique
    deriving (Eq, Ord)

data KindExpr
    = Star
    | KArr KindExpr KindExpr
    deriving (Eq)

data TCon
    = TCon TypeConstructor KindExpr
    deriving ()

data MonoType tvar
    = TyVar tvar
    | TyCon TCon
    | TyApp (MonoType tvar) (MonoType tvar)
    | TyMTV MetaTVar
    deriving (Eq)

data PolyType
    = Forall [SmallId] (MonoType Int)
    deriving ()

data TermExpr dcon annot
    = IVar annot LargeId
    | DCon annot dcon 
    | IApp annot (TermExpr dcon annot) (TermExpr dcon annot)
    | IAbs annot LargeId (TermExpr dcon annot)
    deriving ()

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

instance Show LogicalOperator where
    showsPrec _ logical_operator = case logical_operator of
        LO_ty_pi -> strstr "^"
        LO_if -> strstr ":-"
        LO_true -> strstr "true"
        LO_fail -> strstr "fail"
        LO_cut -> strstr "!"
        LO_and -> strstr ","
        LO_or -> strstr ";"
        LO_imply -> strstr "=>"
        LO_pi -> strstr "pi"
        LO_sigma -> strstr "sigma"

instance Show DataConstructor where
    showsPrec _ data_constructor = case data_constructor of
        DC_LO logical_operator -> showsPrec 0 logical_operator
        DC_Named name -> strstr name
        DC_Unique unique -> showsPrec 0 (unUnique unique)
        DC_Nil -> strstr "[]"
        DC_Cons -> strstr "::"
        DC_ChrL chr -> showsPrec 0 chr
        DC_NatL nat -> showsPrec 0 nat
        DC_Succ -> strstr "S"

instance Show TypeConstructor where
    showsPrec _ type_constructor = case type_constructor of
        TC_Arrow -> strstr "->"
        TC_Named name -> strstr name
        TC_Unique unique -> showsPrec 0 (unUnique unique)

instance Eq TCon where
    TCon type_constructor_1 _ == TCon type_constructor_2 _ = type_constructor_1 == type_constructor_2

instance Ord TCon where
    TCon type_constructor_1 _ `compare` TCon type_constructor_2 _ = type_constructor_1 `compare` type_constructor_2

runUniqueGenT :: Functor m => UniqueGenT m a -> m a
runUniqueGenT = fmap fst . flip runStateT 0 . unUniqueGenT

module Aladdin.Front.Header where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
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

type IVar = Unique

type KindEnv = Map.Map TypeConstructor KindExpr

type TypeEnv = Map.Map DataConstructor PolyType

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
    | DC_Eq
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
    = IVar annot IVar
    | DCon annot dcon 
    | IApp annot (TermExpr dcon annot) (TermExpr dcon annot)
    | IAbs annot IVar (TermExpr dcon annot)
    deriving ()

data Program term
    = Program
        { _KindDecls :: KindEnv
        , _TypeDecls :: TypeEnv
        , _FactDecls :: [term]
        }
    deriving ()

class HasSLoc a where
    getSLoc :: a -> SLoc

class HasAnnot f where
    getAnnot :: f a -> a

class Monad m => GenUniqueM m where
    getNewUnique :: m Unique

instance Semigroup SLoc where
    SLoc pos1 pos2 <> SLoc pos1' pos2' = SLoc (min pos1 pos1') (max pos2 pos2')

instance Show SLoc where
    showsPrec _ = const id

instance Outputable SLoc where
    pprint _ (SLoc (row1, col1) (row2, col2)) = strcat
        [ strstr "("
        , showsPrec 0 row1
        , strstr ","
        , showsPrec 0 col1
        , strstr ") - ("
        , showsPrec 0 row2
        , strstr ","
        , showsPrec 0 col2
        , strstr ")"
        ]

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

instance GenUniqueM m => GenUniqueM (ExceptT s m) where
    getNewUnique = lift getNewUnique

instance GenUniqueM m => GenUniqueM (StateT s m) where
    getNewUnique = lift getNewUnique

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
        DC_Eq -> strstr "="

instance Show TypeConstructor where
    showsPrec _ type_constructor = case type_constructor of
        TC_Arrow -> strstr "->"
        TC_Named name -> strstr name
        TC_Unique unique -> showsPrec 0 (unUnique unique)

instance Read KindExpr where
    readsPrec 0 str0 = [ (kin1 `KArr` kin2, str2) | (kin1, ' ' : '-' : '>' : ' ' : str1) <- readsPrec 1 str0, (kin2, str2) <- readsPrec 0 str1 ] ++ readsPrec 1 str0
    readsPrec 1 ('*' : str0) = [(Star, str0)]
    readsPrec 1 ('(' : str0) = [ (kin, str1) | (kin, ')' : str1) <- readsPrec 0 str0 ]
    readList = undefined

instance Outputable KindExpr where
    pprint 0 (kin1 `KArr` kin2) = pprint 1 kin1 . strstr " -> " . pprint 0 kin2
    pprint 0 kin1 = pprint 1 kin1
    pprint 1 Star = strstr "type"
    pprint 1 kin1 = pprint 2 kin1
    pprint _ kin1 = strstr "(" . pprint 0 kin1 . strstr ")"

instance Eq TCon where
    TCon type_constructor_1 _ == TCon type_constructor_2 _ = type_constructor_1 == type_constructor_2

instance Ord TCon where
    TCon type_constructor_1 _ `compare` TCon type_constructor_2 _ = type_constructor_1 `compare` type_constructor_2

instance Outputable TCon where
    pprint _ (TCon type_constructor _) = showsPrec 0 type_constructor

instance HasAnnot (TermExpr dcon) where
    getAnnot (IVar annot _) = annot
    getAnnot (DCon annot _) = annot
    getAnnot (IApp annot _ _) = annot
    getAnnot (IAbs annot _ _) = annot

runUniqueGenT :: Functor m => UniqueGenT m a -> m a
runUniqueGenT = fmap fst . flip runStateT 0 . unUniqueGenT

mkTyList :: MonoType tvar -> MonoType tvar
mkTyList typ1 = TyApp (TyCon (TCon (TC_Named "list") (read "* -> *"))) typ1

mkTyChr :: MonoType tvar
mkTyChr = TyCon (TCon (TC_Named "char") (read "*"))

mkTyNat :: MonoType tvar
mkTyNat = TyCon (TCon (TC_Named "nat") (read "*"))

mkTyO :: MonoType tvar
mkTyO = TyCon (TCon (TC_Named "o") (read "*"))

mkTyArrow :: MonoType tvar -> MonoType tvar -> MonoType tvar
typ1 `mkTyArrow` typ2 = TyApp (TyApp (TyCon (TCon TC_Arrow (read "* -> * -> *"))) typ1) typ2

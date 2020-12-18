module Aladdin.Front.Header where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Identifier
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique
import Lib.Base

type ErrMsg = String

type SPos = (Int, Int)

type SmallId = String

type LargeId = String

type IVar = Unique

type TVar = SmallId

type MetaTVar = Unique

type KindEnv = Map.Map SmallId KindExpr

type TypeEnv = Map.Map SmallId PolyType

data SLoc
    = SLoc
        { _FirstPos :: SPos
        , _LastPos :: SPos
        }
    deriving (Eq)

data Literal
    = StrLit String
    | ChrLit Char
    | NatLit Integer
    deriving (Eq, Show)

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

data ModuleBody term
    = ModuleBody { _KindDecls :: KindEnv, _TypeDecls :: TypeEnv, _FactDecls :: [term] }
    deriving ()

class HasSLoc a where
    getSLoc :: a -> SLoc

instance Semigroup SLoc where
    loc1 <> loc2 = SLoc { _FirstPos = min (_FirstPos loc1) (_FirstPos loc2), _LastPos = max (_LastPos loc1) (_LastPos loc2) }

instance Outputable SLoc where
    makeOutput _ (SLoc (row1, col1) (row2, col2)) = strstr "(" . showsPrec 0 row1 . strstr ", " . showsPrec 0 col1 . strstr ") - (" . showsPrec 0 row2 . strstr ", " . showsPrec 0 col2 . strstr ")"

instance Show SLoc where
    showsPrec _ _ = id

instance Read KindExpr where
    readsPrec 0 str0 = [ (kin1 `KArr` kin2, str2) | (kin1, ' ' : '-' : '>' : ' ' : str1) <- readsPrec 1 str0, (kin2, str2) <- readsPrec 0 str1 ] ++ readsPrec 1 str0
    readsPrec 1 ('*' : str0) = [(Star, str0)]
    readsPrec _ ('(' : str0) = [ (kin, str1) | (kin, ')' : str1) <- readsPrec 0 str0 ]
    readsPrec _ str0 = []
    readList = undefined

instance Outputable KindExpr where
    makeOutput 0 (kin1 `KArr` kin2) = makeOutput 1 kin1 . strstr " -> " . makeOutput 0 kin2
    makeOutput 0 kin1 = makeOutput 1 kin1
    makeOutput 1 Star = strstr "*"
    makeOutput 1 kin1 = makeOutput 2 kin1
    makeOutput _ kin1 = strstr "(" . makeOutput 0 kin1 . strstr ")"

instance Eq TCon where
    TCon type_constructor_1 _ == TCon type_constructor_2 _ = type_constructor_1 == type_constructor_2

instance Show TCon where
    showsPrec _ (TCon type_constructor _) = showsPrec 0 type_constructor

instance Functor (TermExpr dcon) where
    fmap modify (IVar annot var) = IVar (modify annot) var
    fmap modify (DCon annot con) = DCon (modify annot) con
    fmap modify (IApp annot term1 term2) = IApp (modify annot) (fmap modify term1) (fmap modify term2)
    fmap modify (IAbs annot var term) = IAbs (modify annot) var (fmap modify term)

mkTyArr :: MonoType tvar -> MonoType tvar -> MonoType tvar
typ1 `mkTyArr` typ2 = TyApp (TyApp (TyCon (TCon TC_arrow (read "* -> * -> *"))) typ1) typ2

mkTyO :: MonoType tvar
mkTyO = TyCon (TCon TC_o (read "*"))

mkTyChr :: MonoType tvar
mkTyChr = TyCon (TCon TC_char (read "*"))

mkTyList :: MonoType tvar -> MonoType tvar
mkTyList typ = TyApp (TyCon (TCon TC_list (read "* -> *"))) typ

destructTyArr :: MonoType tvar -> Maybe (MonoType tvar, MonoType tvar)
desturctTyArr (TyApp (TyApp (TyCon (TCon TC_arrow _)) typ1) typ2) = Just (typ1, typ2)
destructTyArr _ = Nothing

getAnnot :: TermExpr dcon annot -> annot
getAnnot (IVar annot _) = annot
getAnnot (DCon annot _) = annot
getAnnot (IApp annot _ _) = annot
getAnnot (IAbs annot _ _) = annot

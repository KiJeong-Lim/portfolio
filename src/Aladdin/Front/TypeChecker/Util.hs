module Aladdin.Front.TypeChecker.Util where

import Aladdin.Front.Header
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

infix 4 +->

infix 4 ->>

data TypeError
    = KindsAreMismatched (MonoType Int, KindExpr) (MonoType Int, KindExpr)
    | OccursCheckFailed MetaTVar (MonoType Int)
    | TypesAreMismatched (MonoType Int) (MonoType Int)
    deriving ()

newtype TypeSubst
    = TypeSubst { getTypeSubst :: Map.Map MetaTVar (MonoType Int) }
    deriving ()

class HasMTVar a where
    getFreeMTVs :: a -> Set.Set MetaTVar -> Set.Set MetaTVar
    substMTVars :: TypeSubst -> a -> a

class IsInt a where
    fromInt :: Int -> a
    toInt :: a -> Int

instance IsInt Int where
    fromInt = id
    toInt = id

instance IsInt tvar => HasMTVar (MonoType tvar) where
    getFreeMTVs (TyMTV mtv) mtvs = Set.insert mtv mtvs
    getFreeMTVs (TyVar tvar) mtvs = mtvs
    getFreeMTVs (TyCon tcon) mtvs = mtvs
    getFreeMTVs (TyApp typ1 typ2) mtvs = getFreeMTVs typ1 (getFreeMTVs typ2 mtvs)
    substMTVars (TypeSubst { getTypeSubst = mapsto }) = go where
        convert :: IsInt tvar => MonoType Int -> MonoType tvar
        convert (TyVar tvar) = TyVar (fromInt tvar)
        convert (TyCon tcon) = TyCon tcon
        convert (TyApp typ1 typ2) = TyApp (convert typ1) (convert typ2)
        convert (TyMTV mtv) = TyMTV mtv
        go :: IsInt tvar => MonoType tvar -> MonoType tvar
        go typ = case typ of
            TyMTV mtv -> case Map.lookup mtv mapsto of
                Nothing -> typ
                Just typ' -> convert typ'
            TyApp typ1 typ2 -> TyApp (go typ1) (go typ2)
            TyVar tvar -> TyVar tvar
            TyCon tcon -> TyCon tcon

instance HasMTVar a => HasMTVar [a] where
    getFreeMTVs = flip (foldr getFreeMTVs)
    substMTVars = map . substMTVars

instance HasMTVar b => HasMTVar (a, b) where
    getFreeMTVs = snd . fmap getFreeMTVs
    substMTVars = fmap . substMTVars

instance HasMTVar a => HasMTVar (Map.Map k a) where
    getFreeMTVs = getFreeMTVs . Map.elems
    substMTVars = Map.map . substMTVars

instance Semigroup TypeSubst where
    theta2 <> theta1 = TypeSubst { getTypeSubst = Map.map (substMTVars theta2) (getTypeSubst theta1) `Map.union` (getTypeSubst theta2) }

instance Monoid TypeSubst where
    mempty = TypeSubst { getTypeSubst = Map.empty }

(+->) :: MetaTVar -> MonoType Int -> Either TypeError TypeSubst
mtv +-> typ 
    | TyMTV mtv == typ = return mempty
    | mtv `Set.member` getFMTVs typ = Left (OccursCheckFailed mtv typ)
    | getKind (TyMTV mtv) == getKind typ = return (TypeSubst (Map.singleton mtv typ))
    | otherwise = Left (KindsAreMismatched (TyMTV mtv, getKind (TyMTV mtv)) (typ, getKind typ))

getFMTVs :: HasMTVar a => a -> Set.Set MetaTVar
getFMTVs = flip getFreeMTVs Set.empty

getKind :: MonoType Int -> KindExpr
getKind = maybe undefined id . go where
    go :: MonoType Int -> Maybe KindExpr
    go (TyVar _) = return Star
    go (TyCon (TCon _ kin)) = return kin
    go (TyApp typ1 typ2) = do
        (kin1 `KArr` kin2) <- go typ1
        return kin2
    go (TyMTV _) = return Star

getMGU :: Monad mnd => MonoType Int -> MonoType Int -> ExceptT ((MonoType Int, MonoType Int), TypeError) mnd TypeSubst
getMGU lhs rhs
    = case go Set.empty lhs rhs of
        (Nothing, theta) -> return theta
        (Just typ_error, theta) -> throwE ((substMTVars theta lhs, substMTVars theta rhs), typ_error)
    where
        go :: Set.Set MetaTVar -> MonoType Int -> MonoType Int -> (Maybe TypeError, TypeSubst)
        go lockeds (TyVar _) _ = error "`getMGU\'"
        go lockeds _ (TyVar _) = error "`getMGU\'"
        go lockeds (TyCon tcon1) (TyCon tcon2)
            | tcon1 == tcon2 = (Nothing, mempty)
        go lockeds (TyMTV mtv) typ 
            | mtv `Set.member` lockeds
            = (Nothing, mempty)
            | otherwise
            = case mtv +-> typ of
                Left typ_error -> (Just typ_error, mempty)
                Right theta -> (Nothing, theta)
        go lockeds typ (TyMTV mtv)
            | mtv `Set.member` lockeds
            = (Nothing, mempty)
            | otherwise
            = case mtv +-> typ of
                Left typ_error -> (Just typ_error, mempty)
                Right theta -> (Nothing, theta)
        go lockeds (TyApp typ1 typ2) (TyApp typ1' typ2') = case go lockeds typ1 typ1' of
            (Nothing, theta1) -> case go lockeds (substMTVars theta1 typ2) (substMTVars theta1 typ2') of
                (Nothing, theta2) -> (Nothing, theta2 <> theta1)
                (Just typ_error, theta2) -> (Just typ_error, theta2 <> theta1)
            (Just (OccursCheckFailed mtv typ), theta1) -> case go (Set.insert mtv lockeds) (substMTVars theta1 typ2) (substMTVars theta1 typ2') of
                (Nothing, theta2) -> (Just (OccursCheckFailed mtv typ), theta2 <> theta1)
                (Just typ_error', theta2) -> (Just typ_error', theta2 <> theta1)
            (Just typ_error, theta1) -> case go lockeds (substMTVars theta1 typ2) (substMTVars theta1 typ2') of
                (Nothing, theta2) -> (Just typ_error, theta2 <> theta1)
                (Just typ_error', theta2) -> (Just typ_error, theta2 <> theta1)
        go lockeds typ1 typ2 = (Just (TypesAreMismatched typ1 typ2), mempty)

unify :: Monad mnd => [(MonoType Int, MonoType Int)] -> ExceptT ((MonoType Int, MonoType Int), TypeError) mnd TypeSubst
unify [] = return mempty
unify ((lhs, rhs) : disgrees) = do
    theta1 <- getMGU lhs rhs
    theta2 <- unify [ (substMTVars theta1 lhs0, substMTVars theta1 rhs0) | (lhs0, rhs0) <- disgrees ]
    return (theta2 <> theta1)

(->>) :: Monad mnd => MonoType Int -> MonoType Int -> ExceptT ((MonoType Int, MonoType Int), TypeError) mnd TypeSubst
lhs ->> rhs
    = case go lhs rhs of
        Right theta -> return theta
        Left typ_error -> throwE ((lhs, rhs), typ_error)
    where
        merge :: TypeSubst -> TypeSubst -> Either (MonoType Int, MonoType Int) TypeSubst
        merge (TypeSubst mapsto1) (TypeSubst mapsto2)
            = case disgrees of
                [] -> Right (TypeSubst (mapsto1 `Map.union` mapsto2))
                (typ1, typ2) : _ -> Left (typ1, typ2)
            where
                disgrees :: [(MonoType Int, MonoType Int)]
                disgrees = do
                    mtv <- Set.toList (Map.keysSet mapsto1 `Set.intersection` Map.keysSet mapsto2)
                    let typ1 = mapsto1 Map.! mtv
                        typ2 = mapsto2 Map.! mtv
                    if typ1 == typ2
                        then []
                        else return (typ1, typ2)
        go :: MonoType Int -> MonoType Int -> Either TypeError TypeSubst
        go (TyVar _) _ = error "`(->>)\'"
        go _ (TyVar _) = error "`(->>)\'"
        go (TyCon tcon1) (TyCon tcon2)
            | tcon1 == tcon2 = return mempty
        go (TyMTV mtv) typ 
            | TyMTV mtv == typ = return mempty
            | getKind (TyMTV mtv) == getKind typ = return (TypeSubst (Map.singleton mtv typ))
            | otherwise = Left (KindsAreMismatched (TyMTV mtv, getKind (TyMTV mtv)) (typ, getKind typ))
        go (TyApp typ1 typ2) (TyApp typ1' typ2') = do
            theta1 <- go typ1 typ1'
            theta2 <- go typ2 typ2'
            case merge theta1 theta2 of
                Left (typ, typ') -> Left (TypesAreMismatched typ typ')
                Right theta -> return theta
        go typ1 typ2 = Left (TypesAreMismatched typ1 typ2)

showMonoType :: Map.Map MetaTVar LargeId -> MonoType Int -> String -> String
showMonoType name_env = go 0 where
    go :: Precedence -> MonoType Int -> String -> String
    go prec (TyApp (TyApp (TyCon (TCon TC_Arrow _)) typ1) typ2)
        | prec <= 0 = go 1 typ1 . strstr " -> " . go 0 typ2
        | otherwise = strstr "(" . go 1 typ1 . strstr " -> " . go 0 typ2 . strstr ")"
    go prec (TyApp typ1 typ2)
        | prec <= 1 = go 1 typ1 . strstr " " . go 2 typ2
        | otherwise = strstr "(" . go 1 typ1 . strstr " " . go 2 typ2 . strstr ")"
    go prec (TyCon con)
        = pprint 0 con
    go prec (TyVar var)
        = strstr "#" . showsPrec 0 var
    go prec (TyMTV mtv)
        = case Map.lookup mtv name_env of
            Nothing -> strstr "mtv_" . showsPrec 0 mtv
            Just name -> strstr name

instantiateScheme :: GenUniqueM m => PolyType -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) ([MetaTVar], MonoType Int)
instantiateScheme = go where
    loop :: [MonoType Int] -> MonoType Int -> MonoType Int
    loop tvars (TyVar idx) = tvars !! idx
    loop tvars (TyCon tcon) = TyCon tcon
    loop tvars (TyApp typ1 typ2) = TyApp (loop tvars typ1) (loop tvars typ2)
    loop tvars (TyMTV mtv) = TyMTV mtv 
    go :: GenUniqueM m => PolyType -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) ([MetaTVar], MonoType Int)
    go (Forall tvars typ) = do
        mtvs <- mapM getNewMTV tvars
        return (mtvs, loop (map TyMTV mtvs) typ)

getNewMTV :: GenUniqueM m => LargeId -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) MetaTVar
getNewMTV largeid
    = do
        used_mtvs_0 <- get
        mtv <- getNewUnique
        let name = makeName used_mtvs_0 largeid
        put (Map.insert mtv name used_mtvs_0)
        return mtv
    where
        makeName :: Map.Map MetaTVar LargeId -> LargeId -> LargeId
        makeName used_mtvs smallid = go 0 where
            go :: Int -> LargeId
            go n = if name `elem` Map.elems used_mtvs then go (n + 1) else name where
                name :: String
                name = smallid ++ "_" ++ show n

zonkMTV :: TypeSubst -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int)
zonkMTV theta = go where
    go :: TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int)
    go (IVar (loc, typ) var) = IVar (loc, substMTVars theta typ) var
    go (DCon (loc, typ) (con, tapps)) = DCon (loc, substMTVars theta typ) (con, substMTVars theta tapps)
    go (IApp (loc, typ) term1 term2) = IApp (loc, substMTVars theta typ) (go term1) (go term2)
    go (IAbs (loc, typ) var term) = IAbs (loc, substMTVars theta typ) var (go term)

mkTyErr :: Map.Map MetaTVar LargeId -> SLoc -> ((MonoType Int, MonoType Int), TypeError) -> ErrMsg
mkTyErr used_mtvs loc ((actual_typ, expected_typ), typ_error) = case typ_error of
    KindsAreMismatched (typ1, kin1) (typ2, kin2) -> concat
        [ "typechecking-error[" ++ pprint 0 loc "]:\n"
        , "  ? expected_typ = `" ++ showMonoType used_mtvs expected_typ ("\', actual_typ = `" ++ showMonoType used_mtvs actual_typ "\';\n")
        , "  ? couldn't solve the equation `" ++ showMonoType used_mtvs typ1 ("\' ~ `" ++ showMonoType used_mtvs typ2 "\',\n")
        , "  ? because the kind of the L.H.S. is `" ++ pprint 0 kin1 ("\' but the kind of the R.H.S. is `" ++ pprint 0 kin2 "\'.\n")
        ]
    OccursCheckFailed mtv1 typ2 -> concat
        [ "typechecking-error[" ++ pprint 0 loc "]:\n"
        , "  ? expected_typ = `" ++ showMonoType used_mtvs expected_typ ("\', actual_typ = `" ++ showMonoType used_mtvs actual_typ "\';\n")
        , "  ? couldn't solve the equation `" ++ showMonoType used_mtvs (TyMTV mtv1) ("\' ~ `" ++ showMonoType used_mtvs typ2 "\',\n")
        , "  ? because occurs check failed.\n"
        ]
    TypesAreMismatched typ1 typ2 -> concat
        [ "typechecking-error[" ++ pprint 0 loc "]:\n"
        , "  ? expected_typ = `" ++ showMonoType used_mtvs expected_typ ("\', actual_typ = `" ++ showMonoType used_mtvs actual_typ "\';\n")
        , "  ? couldn't solve the equation `" ++ showMonoType used_mtvs typ1 ("\' ~ `" ++ showMonoType used_mtvs typ2 "\',\n")
        , "  ? because the types `" ++ showMonoType used_mtvs typ1 ("\' and `" ++ showMonoType used_mtvs typ2 "\' are non-unifiable.\n")
        ]

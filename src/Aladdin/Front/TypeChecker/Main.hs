module Aladdin.Front.TypeChecker.Main where

import Aladdin.Front.Header
import Aladdin.Front.TypeChecker.Util
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

inferType :: GenUniqueM m => TypeEnv -> TermExpr DataConstructor SLoc -> ExceptT ErrMsg m ((TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), Map.Map IVar (MonoType Int)), Map.Map MetaTVar LargeId)
inferType type_env = flip runStateT Map.empty . infer where
    infer :: GenUniqueM m => TermExpr DataConstructor SLoc -> StateT (Map.Map MetaTVar SmallId) (ExceptT ErrMsg m) (TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), Map.Map IVar (MonoType Int))
    infer (IVar loc var) = do
        mtv <- getNewMTV "A"
        return (IVar (loc, TyMTV mtv) var, Map.singleton var (TyMTV mtv))
    infer (DCon loc con) = case con of
        DC_ChrL chr -> return (DCon (loc, mkTyChr) (con, []), Map.empty)
        DC_NatL nat -> return (DCon (loc, mkTyNat) (con, []), Map.empty)
        con -> do
            used_mtvs_0 <- get
            (mtvs, typ) <- case Map.lookup con type_env of
                Nothing -> lift (throwE ("tc-error[" ++ pprint 0 loc ("]:\n  ? the data constructor `" ++ showsPrec 0 con "\' hasn't declared yet.")))
                Just scheme -> instantiateScheme scheme
            return (DCon (loc, typ) (con, map TyMTV mtvs), Map.empty)
    infer (IApp loc term1 term2) = do
        (term1', assumptions1) <- infer term1
        (term2', assumptions2) <- infer term2
        mtv <- getNewMTV "A"
        used_mtvs <- get
        let disagrees = (snd (getAnnot term1'), snd (getAnnot term2') `mkTyArrow` TyMTV mtv) : [ (assumptions1 Map.! mtv0, assumptions2 Map.! mtv0) | mtv0 <- Set.toList (Map.keysSet assumptions1 `Set.intersection` Map.keysSet assumptions2) ]
        theta <- lift $ catchE (unify disagrees) $ throwE . mkTyErr used_mtvs loc
        let used_mtvs' = used_mtvs `Map.withoutKeys` Map.keysSet (getTypeSubst theta)
            assumptions' = substMTVars theta assumptions1 `Map.union` substMTVars theta assumptions2
        put used_mtvs'
        return (zonkMTV theta (IApp (loc, TyMTV mtv) term1' term2'), assumptions')
    infer (IAbs loc var term) = do
        (term', assumptions) <- infer term
        case Map.lookup var assumptions of
            Nothing -> do
                mtv <- getNewMTV "A"
                return (IAbs (loc, TyMTV mtv `mkTyArrow` snd (getAnnot term')) var term', assumptions)
            Just typ -> return (IAbs (loc, typ `mkTyArrow` snd (getAnnot term')) var term', Map.delete var assumptions)

checkType :: GenUniqueM m => TypeEnv -> TermExpr DataConstructor SLoc -> MonoType Int -> ExceptT ErrMsg m (TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), (Map.Map MetaTVar LargeId, Map.Map IVar (MonoType Int)))
checkType type_env term expected_typ = do
    ((term', assumptions), used_mtvs) <- inferType type_env term
    let actual_typ = snd (getAnnot term')
    theta <- catchE (actual_typ ->> expected_typ) $ throwE . mkTyErr used_mtvs (getAnnot term)
    let used_mtvs' = used_mtvs `Map.withoutKeys` Map.keysSet (getTypeSubst theta)
        assumptions' = substMTVars theta assumptions
    return (zonkMTV theta term', (used_mtvs', assumptions'))

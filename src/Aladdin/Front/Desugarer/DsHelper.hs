module Aladdin.Front.Desugarer.DsHelper where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Identifier
import Aladdin.Front.Analyzer.Grammar
import Aladdin.Front.Header
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique
import Lib.Base

makeKindEnv :: [(SLoc, (SmallId, KindRep))] -> KindEnv -> ExceptT ErrMsg IO KindEnv
makeKindEnv = go where
    krank :: KindExpr -> Int
    krank Star = 0
    krank (kin1 `KArr` kin2) = max (krank kin1 + 1) (krank kin2)
    unRep :: KindRep -> ExceptT ErrMsg IO KindExpr
    unRep krep = do
        (kin, loc) <- case krep of
            RStar loc -> return (Star, loc)
            RKArr loc krep1 krep2 -> do
                kin1 <- unRep krep1
                kin2 <- unRep krep2
                return (kin1 `KArr` kin2, loc)
            RKInd loc krep -> do
                kin <- unRep krep
                return (kin, loc)
        if krank kin > 1
            then throwE ("ds-error: higher-order kinded type at " ++ makeOutput 0 loc (" is not allowed: at " ++ makeOutput 0 loc "."))
            else return kin
    go :: [(SLoc, (SmallId, KindRep))] -> KindEnv -> ExceptT ErrMsg IO KindEnv
    go [] kind_env = return kind_env
    go ((loc, (tcon, krep)) : triples) kind_env
        | otherwise = case Map.lookup tcon kind_env of
            Just _ -> throwE ("ds-error: redeclare the already declared type construtor `" ++ showsPrec 0 tcon ("\' at " ++ makeOutput 0 loc "."))
            Nothing -> do
                kin <- unRep krep
                go triples (Map.insert tcon kin kind_env)

makeTypeEnv :: KindEnv -> [(SLoc, (SmallId, TypeRep))] -> TypeEnv -> ExceptT ErrMsg IO TypeEnv
makeTypeEnv kind_env = go where
    modus_ponens :: KindExpr -> KindExpr -> Either ErrMsg KindExpr
    modus_ponens (kin1 `KArr` kin2) kin3
        | kin1 == kin3 = Right kin2
    modus_ponens (kin1 `KArr` kin2) kin3 = Left ("couldn't solve `" ++ makeOutput 0 kin1 ("\' ~ `" ++ makeOutput 0 kin3 "\'"))
    modus_ponens Star kin1 = Left ("coudln't solve `*\' ~ `" ++ makeOutput 1 kin1 " -> _\'")
    unRep :: TypeRep -> ExceptT ErrMsg IO (KindExpr, MonoType SmallId)
    unRep trep = case trep of
        RTyVar loc tvrep -> return (Star, TyVar tvrep)
        RTyCon loc "string" -> return (Star, mkTyList mkTyChr)
        RTyCon loc tcrep -> case Map.lookup tcrep kind_env of
            Nothing -> throwE ("ds-error: the type constructor `" ++ showsPrec 0 tcrep ("\' at " ++ makeOutput 0 loc " hasn't declared."))
            Just kin -> return (kin, TyCon (TCon (TC_Named (ID_Name tcrep)) kin))
        RTyApp loc trep1 trep2 -> do
            (kin1, typ1) <- unRep trep1
            (kin2, typ2) <- unRep trep2
            case modus_ponens kin1 kin2 of
                Left msg -> throwE ("ds-error: kinds are mismatched at " ++ makeOutput 0 loc (", because " ++ msg ++ "."))
                Right kin -> return (kin, TyApp typ1 typ2)
        RTyArr loc trep1 trep2 -> do
            (kin1, typ1) <- unRep trep1
            (kin2, typ2) <- unRep trep2
            case [ "couldn't solve `" ++ makeOutput 0 kin "\' ~ `*\'" | kin <- [kin1, kin2], kin /= Star ] of
                [] -> return (Star, typ1 `mkTyArr` typ2)
                msg : _ -> throwE ("ds-error: kinds are mismatched at " ++ makeOutput 0 loc (", because " ++ msg ++ "."))
        RTyInd loc trep -> unRep trep
    generalize :: MonoType SmallId -> PolyType
    generalize typ = Forall tvars (indexify typ) where
        getFreeTVs :: MonoType SmallId -> Set.Set SmallId
        getFreeTVs (TyVar tvar) = Set.singleton tvar
        getFreeTVs (TyCon tcon) = Set.empty
        getFreeTVs (TyApp typ1 typ2) = getFreeTVs typ1 `Set.union` getFreeTVs typ2
        getFreeTVs (TyMTV mtv) = Set.empty
        tvars :: [SmallId]
        tvars = Set.toAscList (getFreeTVs typ)
        indexify :: MonoType SmallId -> MonoType Int
        indexify (TyVar tvar) = case tvar `List.elemIndex` tvars of
            Nothing -> error "`indexify\'"
            Just idx -> TyVar idx
        indexify (TyCon tcon) = TyCon tcon
        indexify (TyApp typ1 typ2) = TyApp (indexify typ1) (indexify typ2)
        indexify (TyMTV mtv) = TyMTV mtv
    go :: [(SLoc, (SmallId, TypeRep))] -> TypeEnv -> ExceptT ErrMsg IO TypeEnv
    go [] type_env = return type_env
    go ((loc, (con, trep)) : triples) type_env = case Map.lookup con type_env of
        Just _ -> throwE ("ds-error: redeclare the already declared constant `" ++ con ++ "\' at " ++ makeOutput 0 loc ".")
        Nothing -> do
            (kin, typ) <- unRep trep
            let msg = "couldn't solve `" ++ makeOutput 0 kin "\' ~ `*\'"
            if kin == Star
                then go triples (Map.insert con (generalize typ) type_env)
                else throwE ("ds-error: kinds are mismatched at " ++ makeOutput 0 loc (", because " ++ msg ++ "."))

desugarTerm :: TermRep -> StateT (Map.Map SmallId IVar) (ExceptT ErrMsg IO) (TermExpr LargeId SLoc)
desugarTerm (RVar loc1 "_") = do
    var <- lift (lift newUnique)
    return (IVar loc1 var)
desugarTerm (RVar loc1 var_rep) = do
    env <- get
    case Map.lookup var_rep env of
        Nothing -> do
            var <- lift (lift newUnique)
            put (Map.insert var_rep var env)
            return (IVar loc1 var)
        Just var -> return (IVar loc1 var)
desugarTerm (RCon loc1 con_rep) = return (DCon loc1 con_rep)
desugarTerm (RApp loc1 term_rep_1 term_rep_2) = do
    term_1 <- desugarTerm term_rep_1
    term_2 <- desugarTerm term_rep_2
    return (IApp loc1 term_1 term_2)
desugarTerm (RAbs loc1 var_rep term_rep) = do
    var <- lift (lift newUnique)
    env <- get
    case Map.lookup var_rep env of
        Nothing -> do
            put (Map.insert var_rep var env)
            term <- desugarTerm term_rep
            modify (Map.delete var_rep)
            return (IAbs loc1 var term)
        Just var' -> do
            put (Map.insert var_rep var (Map.delete var_rep env))
            term <- desugarTerm term_rep
            modify (Map.insert var_rep var' . Map.delete var_rep)
            return (IAbs loc1 var term)
desugarTerm (RInd loc1 term_rep) = desugarTerm term_rep

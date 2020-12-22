module Aladdin.Front.Desugarer.ForType where

import Aladdin.Front.Analyzer.Grammar
import Aladdin.Front.Header
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

makeTypeEnv :: KindEnv -> [(SLoc, (DataConstructor, TypeRep))] -> TypeEnv -> Either ErrMsg TypeEnv
makeTypeEnv kind_env = go where
    applyModusPonens :: KindExpr -> KindExpr -> Either ErrMsg KindExpr
    applyModusPonens (kin1 `KArr` kin2) kin3
        | kin1 == kin3 = Right kin2
    modus_ponens (kin1 `KArr` kin2) kin3 = Left ("  ? couldn't solve `" ++ pprint 0 kin1 ("\' ~ `" ++ pprint 0 kin3 "\'"))
    modus_ponens Star kin1 = Left ("  ? coudln't solve `type\' ~ `" ++ pprint 1 kin1 " -> _\'")
    unRep :: TypeRep -> Either ErrMsg (KindExpr, MonoType LargeId)
    unRep trep = case trep of
        RTyVar loc tvrep -> return (Star, TyVar tvrep)
        RTyCon loc (TC_Named "string") -> return (Star, mkTyList mkTyChr)
        RTyCon loc type_constructor -> case Map.lookup type_constructor kind_env of
            Nothing -> Left ("desugaring-error[" ++ pprint 0 loc ("]:\n  ? the type constructor `" ++ showsPrec 0 type_constructor "hasn't declared.\n"))
            Just kin -> return (kin, TyCon (TCon type_constructor kin))
        RTyApp loc trep1 trep2 -> do
            (kin1, typ1) <- unRep trep1
            (kin2, typ2) <- unRep trep2
            case modus_ponens kin1 kin2 of
                Left msg -> Left ("desugaring-error[" ++ pprint 0 loc ("]:\n " ++ msg ++ ".\n"))
                Right kin -> return (kin, TyApp typ1 typ2)
        RTyPrn loc trep -> unRep trep
    generalize :: MonoType LargeId -> PolyType
    generalize typ = Forall tvars (indexify typ) where
        getFreeTVs :: MonoType LargeId -> Set.Set LargeId
        getFreeTVs (TyVar tvar) = Set.singleton tvar
        getFreeTVs (TyCon tcon) = Set.empty
        getFreeTVs (TyApp typ1 typ2) = getFreeTVs typ1 `Set.union` getFreeTVs typ2
        getFreeTVs (TyMTV mtv) = Set.empty
        tvars :: [LargeId]
        tvars = Set.toAscList (getFreeTVs typ)
        indexify :: MonoType LargeId -> MonoType Int
        indexify (TyVar tvar) = case tvar `List.elemIndex` tvars of
            Nothing -> error "unreachable!"
            Just idx -> TyVar idx
        indexify (TyCon tcon) = TyCon tcon
        indexify (TyApp typ1 typ2) = TyApp (indexify typ1) (indexify typ2)
        indexify (TyMTV mtv) = TyMTV mtv
    hasValidHead :: MonoType LargeId -> Bool
    hasValidHead = go2 . go1 where
        go1 :: MonoType LargeId -> MonoType LargeId
        go1 (TyApp (TyApp (TyCon (TCon TC_Arrow _)) typ1) typ2) = go1 typ2
        go1 typ1 = typ1
        go2 :: MonoType LargeId -> Bool
        go2 (TyCon _) = True
        go2 (TyApp typ _) = go2 typ
        go2 _ = False
    go :: [(SLoc, (DataConstructor, TypeRep))] -> TypeEnv -> Either ErrMsg TypeEnv
    go [] type_env = return type_env
    go ((loc, (con, trep)) : triples) type_env = case Map.lookup con type_env of
        Nothing -> do
            (kin, typ) <- unRep trep
            if kin == Star
                then if hasValidHead typ
                    then go triples (Map.insert con (generalize typ) type_env)
                    else Left ("desugaring-error[" ++ pprint 0 loc ("]:\n  ? the type of `" ++ showsPrec 0 con "\' is invalid.\n"))
                else Left ("desugaring-error[" ++ pprint 0 loc ("]:\n  ? couldn't solve `" ++ pprint 0 kin "\' ~ `type\'.\n"))
        _ -> Left ("desugaring-error[" ++ pprint 0 loc ("]:\n  ? it is wrong to redeclare the already declared constant `" ++ showsPrec 0 con "\'.\n"))

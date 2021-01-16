module Aladdin.Back.Converter.Scheme where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Converter.Util
import Aladdin.Front.Header
import Aladdin.Front.TypeChecker.Util
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

type ExpectedAs = String

type DeBruijnIndicesEnv = [Unique]

type FreeVariableEnv = Map.Map Unique TermNode

convertVar :: FreeVariableEnv -> DeBruijnIndicesEnv -> IVar -> TermNode
convertVar var_name_env env var = case var `List.elemIndex` env of
    Nothing -> var_name_env Map.! var
    Just idx -> mkNIdx (idx + 1)

convertType :: FreeVariableEnv -> DeBruijnIndicesEnv -> MonoType Int -> TermNode
convertType var_name_env env (TyMTV mtv) = convertVar var_name_env env mtv
convertType var_name_env env (TyApp typ1 typ2) = mkNApp (convertType var_name_env env typ1) (convertType var_name_env env typ2)
convertType var_name_env env (TyCon (TCon tc _)) = mkNCon tc 
convertType var_name_env env (TyVar _) = error "`convertType\'"

convertCon :: FreeVariableEnv -> DeBruijnIndicesEnv -> DataConstructor -> [MonoType Int] -> TermNode
convertCon var_name_env env con tapps = List.foldl' mkNApp (mkNCon con) (map (convertType var_name_env env) tapps)

convertWithoutChecking :: GenUniqueM m => FreeVariableEnv -> DeBruijnIndicesEnv -> ExpectedAs -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertWithoutChecking var_name_env = go where
    loop :: DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> TermNode
    loop env (DCon loc (DC_LO logical_operator, tapps))
        = mkNCon logical_operator
    loop env (IVar loc var)
        = convertVar var_name_env env var
    loop env (DCon loc (data_constructor, tapps))
        = convertCon var_name_env env data_constructor tapps
    loop env (IApp loc term1 term2)
        = mkNApp (loop env term1) (loop env term2)
    loop env (IAbs loc var1 term2)
        = mkNAbs (loop (var1 : env) term2)
    go :: GenUniqueM m => DeBruijnIndicesEnv -> ExpectedAs -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
    go env expected_as = return . loop env . reduceTermExpr

convertWithChecking :: GenUniqueM m => FreeVariableEnv -> DeBruijnIndicesEnv -> ExpectedAs -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertWithChecking var_name_env = go where
    check :: GenUniqueM m => DeBruijnIndicesEnv -> ExpectedAs -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
    check env expected_as term
        = case expected_as of
            "fact" -> case unFoldIApp term of
                (DCon (loc, typ) (DC_LO LO_pi, tapps), args) -> case (tapps, args) of
                    ([typ1], [term1]) -> do
                        var <- getNewUnique
                        term1' <- check (var : env) "fact" (reduceTermExpr (IApp (fst (getAnnot term1), mkTyO) term1 (IVar (fst (getAnnot term1), typ1) var)))
                        let result = mkNApp (mkNCon LO_pi) (mkNAbs term1')
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_sigma, tapps), args) -> raise
                (DCon (loc, typ) (DC_LO LO_if, tapps), args) -> case args of
                    [term1, term2] -> do
                        term1' <- check env "fact" term1
                        term2' <- check env "goal" term2
                        let result = mkNApp (mkNApp (mkNCon LO_if) term1') term2'
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_and, tapps), args) -> raise
                (DCon (loc, typ) (DC_LO LO_or, tapps), args) -> raise
                (DCon (loc, typ) (DC_LO LO_imply, tapps), args) -> raise
                (DCon (loc, typ) (DC_LO LO_true, tapps), args) -> raise
                (DCon (loc, typ) (DC_LO LO_fail, tapps), args) -> raise
                (DCon (loc, typ) (DC_LO LO_cut, tapps), args) -> raise
                (DCon (loc, typ) (con, tapps), args)
                    | isPredicate typ -> do
                        terms' <- mapM (check env "term") args
                        let result = List.foldl' mkNApp (convertCon var_name_env env con tapps) terms'
                        result `seq` return result
                _ -> raise
            "query" -> case unFoldIApp term of
                (DCon (loc, typ) (DC_LO LO_pi, tapps), args) -> case (tapps, args) of
                    ([typ1], [term1]) -> do
                        var <- getNewUnique
                        term1' <- check (var : env) "query" (reduceTermExpr (IApp (fst (getAnnot term1), mkTyO) term1 (IVar (fst (getAnnot term1), typ1) var)))
                        let result = mkNApp (mkNCon LO_pi) (mkNAbs term1')
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_sigma, tapps), args) -> case args of
                    [term1] -> do
                        var <- getNewUnique
                        term1' <- check (var : env) "query" (reduceTermExpr (IApp (fst (getAnnot term1), mkTyO) term1 (IVar (fst (getAnnot term1), typ) var)))
                        let result = mkNApp (mkNCon LO_sigma) (mkNAbs term1')
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_if, tapps), args) -> raise
                (DCon (loc, typ) (DC_LO LO_and, tapps), args) -> case args of
                    [term1, term2] -> do
                        term1' <- check env "query" term1
                        term2' <- check env "query" term2
                        let result = mkNApp (mkNApp (mkNCon LO_and) term1') term2'
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_or, tapps), args) -> case args of
                    [term1, term2] -> do
                        term1' <- check env "query" term1
                        term2' <- check env "query" term2
                        let result = mkNApp (mkNApp (mkNCon LO_or) term1') term2'
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_imply, tapps), args) -> case args of
                    [term1, term2] -> do
                        term1' <- check env "fact" term1
                        term2' <- check env "query" term2
                        let result = mkNApp (mkNApp (mkNCon LO_imply) term1') term2'
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_true, tapps), args) -> case args of
                    [] -> do
                        let result = mkNCon LO_true
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_fail, tapps), args) -> case args of
                    [] -> do
                        let result = mkNCon LO_fail
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_cut, tapps), args) -> case args of
                    [] -> do
                        let result = mkNCon LO_cut
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (con, tapps), args)
                    | isPredicate typ -> do
                        terms' <- mapM (check env "term") args
                        let result = List.foldl' mkNApp (convertCon var_name_env env con tapps) terms'
                        result `seq` return result
                _ -> raise
            "goal" -> case unFoldIApp term of
                (DCon (loc, typ) (DC_LO LO_pi, tapps), args) -> case (tapps, args) of
                    ([typ1], [term1]) -> do
                        var <- getNewUnique
                        term1' <- check (var : env) "goal" (reduceTermExpr (IApp (fst (getAnnot term1), mkTyO) term1 (IVar (fst (getAnnot term1), typ1) var)))
                        let result = mkNApp (mkNCon LO_pi) (mkNAbs term1')
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_sigma, tapps), args) -> case args of
                    [term1] -> do
                        var <- getNewUnique
                        term1' <- check (var : env) "goal" (reduceTermExpr (IApp (fst (getAnnot term1), mkTyO) term1 (IVar (fst (getAnnot term1), typ) var)))
                        let result = mkNApp (mkNCon LO_sigma) (mkNAbs term1')
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_if, tapps), args) -> raise
                (DCon (loc, typ) (DC_LO LO_and, tapps), args) -> case args of
                    [term1, term2] -> do
                        term1' <- check env "goal" term1
                        term2' <- check env "goal" term2
                        let result = mkNApp (mkNApp (mkNCon LO_and) term1') term2'
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_or, tapps), args) -> case args of
                    [term1, term2] -> do
                        term1' <- check env "goal" term1
                        term2' <- check env "goal" term2
                        let result = mkNApp (mkNApp (mkNCon LO_or) term1') term2'
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_imply, tapps), args) -> case args of
                    [term1, term2] -> do
                        term1' <- check env "fact" term1
                        term2' <- check env "goal" term2
                        let result = mkNApp (mkNApp (mkNCon LO_imply) term1') term2'
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_true, tapps), args) -> case args of
                    [] -> do
                        let result = mkNCon LO_true
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_fail, tapps), args) -> case args of
                    [] -> do
                        let result = mkNCon LO_fail
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (DC_LO LO_cut, tapps), args) -> case args of
                    [] -> do
                        let result = mkNCon LO_cut
                        result `seq` return result
                    _ -> raise
                (DCon (loc, typ) (con, tapps), args)
                    | isPredicate typ -> do
                        terms' <- mapM (check env "term") args
                        let result = List.foldl' mkNApp (convertCon var_name_env env con tapps) terms'
                        result `seq` return result
                (IVar _ var, args) -> do
                    terms' <- mapM (check env "term") args
                    let result = List.foldl' mkNApp (convertVar var_name_env env var) terms'
                    result `seq` return result
                _ -> raise
            "term" -> case viewIAbs term of
                (vars', term')
                    | mkTyO == snd (getAnnot term') -> do
                        terms' <- (check (vars' ++ env) "goal" term')
                        let result = foldr ($) terms' (replicate (length vars') mkNAbs)
                        result `seq` return result
                    | otherwise -> case unFoldIApp term' of
                        (IVar _ var, args) -> do
                            terms' <- mapM (check (vars' ++ env) "term") args
                            let result = foldr ($) (List.foldl' mkNApp (convertVar var_name_env (vars' ++ env) var) terms') (replicate (length vars') mkNAbs)
                            result `seq` return result
                        (DCon typ (con, tapps), args) -> do
                            terms' <- mapM (check (vars' ++ env) "term") args
                            let result = foldr ($) (List.foldl' mkNApp (convertCon var_name_env (vars' ++ env) con tapps) terms') (replicate (length vars') mkNAbs)
                            result `seq` return result
                        _ -> raise
            _ -> undefined
        where
            raise :: GenUniqueM m => ExceptT ErrMsg m TermNode
            raise = throwE ("converting-error[" ++ pprint 0 (fst (getAnnot term)) ("]:\n  ? expected_as = " ++ expected_as ++ ".\n"))
    go :: GenUniqueM m => DeBruijnIndicesEnv -> ExpectedAs -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
    go env expected_as = check env expected_as . reduceTermExpr

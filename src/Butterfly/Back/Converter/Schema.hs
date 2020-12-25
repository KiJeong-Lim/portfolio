module Butterfly.Back.Converter.Schema where

import Butterfly.Back.Base.CoreTerm
import Butterfly.Back.Base.Instruction
import Butterfly.Back.Base.Util
import Butterfly.Back.Converter.Util
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

runCompiler :: CoreTops IVar (GuaranteeIVarRenamed, FreeVars) -> StateT Converter (ExceptT ConvertErr Identity) ()
runCompiler tops = sequence [ compileSC var | (var, (params, rhs)) <- tops ] *> pure () where
    runSchemeOfConstruction :: VarIdxEnv -> CoreTerm IVar (GuaranteeIVarRenamed, FreeVars) -> WriterT GmCode (StateT Converter (ExceptT ConvertErr Identity)) ()
    runSchemeOfConstruction env (CT_Var (g, fvs) var)
        = case VI_var var `List.elemIndex` env of
            Nothing -> do
                (fun_adr, arity) <- lift $ StateT $ flip catchE (const (throwE (CannotFindVar var env))) . runStateT (compileSC var)
                tell [GI_mk_fun (fun_adr, arity)]
                return ()
            Just idx -> do
                tell [GI_mk_var idx]
                return ()
    runSchemeOfConstruction env (CT_Con (g, fvs) tag)
        = do
            tell [GI_mk_con tag]
            return ()
    runSchemeOfConstruction env (CT_App (g, fvs) term1 term2)
        = do
            runSchemeOfConstruction env term2
            runSchemeOfConstruction (VI_dummy : env) term1
            tell [GI_mk_app]
            return ()
    runSchemeOfConstruction env (CT_Let (g, fvs) (is_rec, defns) body)
        | is_rec = do
            tell [GI_alloc n]
            sequence
                [ do
                    runSchemeOfConstruction env' rhs
                    tell [GI_update (n - i)]
                    return ()
                | (i, (var, (params, rhs))) <- zip [1, 2 .. n] defns
                ]
            runSchemeOfConstruction env' body
            tell [GI_slide n]
            return ()
        | otherwise = do
            sequence
                [ runSchemeOfConstruction (replicate i VI_dummy ++ env) rhs
                | (i, (var, (params, rhs))) <- zip [0, 1 .. n - 1] defns
                ]
            runSchemeOfConstruction env' body
            tell [GI_slide n]
            return ()
        where
            n :: Int
            n = length defns
            env' :: VarIdxEnv
            env' = map (VI_var . fst) defns ++ env
    runSchemeOfConstruction env (CT_Mat (g, fvs) body altns)
        = case Set.toList fvs of
            [] -> undefined
            args -> do
                code <- lift (runSchemeOfReturning (args, CT_Mat (g, fvs) body altns))
                converter0 <- lift get
                let fun_adr = getAdrForNextSC converter0
                lift (put (converter0 { getAdrForNextSC = fun_adr + 1, bindsGmCodeToSC = Map.insert fun_adr code (bindsGmCodeToSC converter0) }))
                tell [GI_mk_fun (fun_adr, length args)]
                sequence
                    [ case VI_var var `List.elemIndex` (VI_dummy : env) of
                        Nothing -> lift (lift (throwE (CannotFindVar var (VI_dummy : env))))
                        Just idx -> do
                            tell [GI_mk_var idx]
                            tell [GI_mk_app]
                            return ()
                    | var <- args
                    ]
                return ()
    runSchemeOfConstruction env (CT_Lam (g, fvs) (params, body))
        | null params = do
            runSchemeOfConstruction env body
            return ()
        | otherwise = do
            let n = length params
            tell [GI_alloc n]
            runSchemeOfConstruction (map VI_var params ++ env) body
            tell (replicate n GI_mk_lam)
            return ()
    runSchemeOfEvaluation :: VarIdxEnv -> CoreTerm IVar (GuaranteeIVarRenamed, FreeVars) -> WriterT GmCode (StateT Converter (ExceptT ConvertErr Identity)) ()
    runSchemeOfEvaluation env (CT_Var (g, fvs) var)
        = case VI_var var `List.elemIndex` env of
            Nothing -> do
                fun_adr <- lift $ StateT $ flip catchE (const (throwE (CannotFindVar var env))) . runStateT (compileSC var)
                tell [GI_mk_fun fun_adr, GI_eval]
                return ()
            Just idx -> do
                tell [GI_mk_var idx, GI_eval]
                return ()
    runSchemeOfEvaluation env (CT_Con (g, fvs) tag)
        = do
            tell [GI_mk_con tag]
            return ()
    runSchemeOfEvaluation env (CT_App (g, fvs) term1 term2)
        = do
            runSchemeOfConstruction env term2
            runSchemeOfConstruction (VI_dummy : env) term1
            tell [GI_mk_app, GI_eval]
            return ()
    runSchemeOfEvaluation env (CT_Let (g, fvs) (is_rec, defns) body)
        | is_rec = do
            tell [GI_alloc n]
            sequence
                [ do
                    runSchemeOfConstruction env' rhs
                    tell [GI_update (n - i)]
                    return ()
                | (i, (var, (params, rhs))) <- zip [1, 2 .. n] defns
                ]
            runSchemeOfEvaluation env' body
            tell [GI_slide n]
            return ()
        | otherwise = do
            sequence
                [ runSchemeOfConstruction (replicate i VI_dummy ++ env) rhs
                | (i, (var, (params, rhs))) <- zip [0, 1 .. n - 1] defns
                ]
            runSchemeOfEvaluation env' body
            tell [GI_slide n]
            return ()
        where
            n :: Int
            n = length defns
            env' :: VarIdxEnv
            env' = map (VI_var . fst) defns ++ env
    runSchemeOfEvaluation env (CT_Mat (g, fvs) body altns)
        = do
            runSchemeOfEvaluation env body
            tagged_codes <- sequence
                [ do
                    (_, code) <- lift (runWriterT (runSchemeOfEvaluation (map VI_var params ++ env) rhs))
                    return (tag, code)
                | (tag, (params, rhs)) <- altns
                ]
            tell [GI_jump tagged_codes]
            return ()
    runSchemeOfEvaluation env (CT_Lam (g, fvs) (params, body))
        | null params = do
            runSchemeOfEvaluation env body
            return ()
        | otherwise = do
            let n = length params
            tell [GI_alloc n]
            runSchemeOfConstruction (map VI_var params ++ env) body
            tell (replicate n GI_mk_lam)
            return ()
    runSchemeOfReturning :: CoreAbsn IVar (GuaranteeIVarRenamed, FreeVars) -> StateT Converter (ExceptT ConvertErr Identity) GmCode
    runSchemeOfReturning (params, rhs) = do
        let d = length params
            env = map VI_var params
        (_, code) <- runWriterT (runSchemeOfEvaluation env rhs)
        return (code ++ [GI_update d, GI_pop d])
    compileSC :: SC -> StateT Converter (ExceptT ConvertErr Identity) (AdrOf SC, Arity)
    compileSC var = case lookup var tops of
        Nothing -> lift (throwE (CannotFindSC var))
        Just (params, rhs) -> case length params of
            0 -> undefined
            arity -> do
                converter0 <- get
                case Map.lookup var (getAdrOfNamedSC converter0) of
                    Nothing -> do
                        let fun_adr = getAdrForNextSC converter0
                        put (converter0 { getAdrForNextSC = fun_adr + 1, getAdrOfNamedSC = Map.insert var fun_adr (getAdrOfNamedSC converter0) })
                        code <- runSchemeOfReturning (params, rhs)
                        converter1 <- get
                        put (converter1 { bindsGmCodeToSC = Map.insert fun_adr code (bindsGmCodeToSC converter1) })
                        return (fun_adr, arity)
                    Just fun_adr -> return (fun_adr, arity)

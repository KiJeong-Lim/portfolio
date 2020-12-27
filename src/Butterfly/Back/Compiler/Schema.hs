module Butterfly.Back.Compiler.Schema where

import Butterfly.Back.Base.CoreTerm
import Butterfly.Back.Base.Instruction
import Butterfly.Back.Base.Util
import Butterfly.Back.Compiler.Util
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

runSchemeOfTermConstruction :: CoreTops IVar (GuaranteeIVarRenamed, FreeVars) -> LocalIdxEnv -> CoreTerm IVar (GuaranteeIVarRenamed, FreeVars) -> WriterT GmCode (StateT Compiler (ExceptT CompileErr Identity)) ()
runSchemeOfTermConstruction tops idx_env (CT_Var (g, fvs) var)
    = case LI_var var `List.elemIndex` idx_env of
        Nothing -> do
            (fun_adr, arity) <- lift $ StateT $ flip catchE (const (throwE (CE_cannot_find_var var idx_env))) . runStateT (compileSupercombinator tops var)
            tell [GI_push_fun (fun_adr, arity)]
            return ()
        Just idx -> do
            tell [GI_push idx]
            return ()
runSchemeOfTermConstruction tops idx_env (CT_Con (g, fvs) tag)
    = do
        tell [GI_push_con tag]
        return ()
runSchemeOfTermConstruction tops idx_env (CT_App (g, fvs) term1 term2)
    = do
        runSchemeOfTermConstruction tops idx_env term2
        runSchemeOfTermConstruction tops (LI_dummy : idx_env) term1
        tell [GI_mk_app]
        return ()
runSchemeOfTermConstruction tops idx_env (CT_Let (g, fvs) (is_rec, defns) body)
    = do
        let n = length defns
            idx_env' = replicate n LI_dummy ++ idx_env
        if is_rec
            then do
                tell [GI_alloc n]
                sequence
                    [ case length params of
                        0 -> do
                            runSchemeOfTermConstruction tops idx_env' rhs
                            tell [GI_update (n - 1 - i)]
                            return ()
                        arity -> do
                            tell [GI_alloc arity]
                            runSchemeOfTermConstruction tops (map LI_var params ++ idx_env') rhs
                            tell (replicate arity GI_mk_abs)
                            tell [GI_update (n - 1 - i)]
                            return ()
                    | (i, (var, (params, rhs))) <- zip [0, 1 .. n - 1] defns
                    ]
                return ()
            else do
                sequence
                    [ case length params of
                        0 -> do
                            runSchemeOfTermConstruction tops (replicate i LI_dummy ++ idx_env) rhs
                            return ()
                        arity -> do
                            tell [GI_alloc arity]
                            runSchemeOfTermConstruction tops (map LI_var params ++ replicate i LI_dummy ++ idx_env) rhs
                            tell (replicate arity GI_mk_abs)
                            return ()
                    | (i, (var, (params, rhs))) <- zip [0, 1 .. n - 1] defns
                    ]
                return ()
        runSchemeOfTermConstruction tops idx_env' body
        tell [GI_slide n]
        return ()
runSchemeOfTermConstruction tops idx_env (CT_Mat (g, fvs) body altns)
    = do
        compiler <- lift get
        let fun_adr = getNextFunAdr compiler
            params = Set.toList fvs
            arity = length params
            rhs = CT_Mat (g, fvs) body altns
        lift (put (compiler { getNextFunAdr = fun_adr + 1 }))
        lift (runSchemeOfSupercombinator tops fun_adr (params, rhs))
        sequence
            [ do
                let idx_env' = replicate i LI_dummy ++ idx_env
                case LI_var var `List.elemIndex` idx_env' of
                    Nothing -> lift (lift (throwE (CE_cannot_find_var var idx_env')))
                    Just idx -> tell [GI_push idx]
                return ()
            | (i, var) <- zip [0, 1 .. arity - 1] params
            ]
        tell [GI_push_fun (fun_adr, arity)]
        tell (replicate arity GI_mk_app)
        return ()
runSchemeOfTermConstruction tops idx_env (CT_Lam (g, fvs) (params, body))
    = case length params of
        0 -> do
            runSchemeOfTermConstruction tops idx_env body
            return ()
        arity -> do
            tell [GI_alloc arity]
            runSchemeOfTermConstruction tops (map LI_var params ++ idx_env) body
            tell (replicate arity GI_mk_abs)
            return ()

runSchemeOfTermEvaluation :: CoreTops IVar (GuaranteeIVarRenamed, FreeVars) -> LocalIdxEnv -> CoreTerm IVar (GuaranteeIVarRenamed, FreeVars) -> WriterT GmCode (StateT Compiler (ExceptT CompileErr Identity)) ()
runSchemeOfTermEvaluation tops idx_env (CT_Var (g, fvs) var)
    = case LI_var var `List.elemIndex` idx_env of
        Nothing -> do
            (fun_adr, arity) <- lift $ StateT $ flip catchE (const (throwE (CE_cannot_find_var var idx_env))) . runStateT (compileSupercombinator tops var)
            tell [GI_push_fun (fun_adr, arity), GI_eval]
            return ()
        Just idx -> do
            tell [GI_push idx, GI_eval]
            return ()
runSchemeOfTermEvaluation tops idx_env (CT_Con (g, fvs) tag)
    = do
        tell [GI_push_con tag]
        return ()
runSchemeOfTermEvaluation tops idx_env (CT_App (g, fvs) term1 term2)
    = do
        runSchemeOfTermConstruction tops idx_env term2
        runSchemeOfTermConstruction tops (LI_dummy : idx_env) term1
        tell [GI_mk_app, GI_eval]
        return ()
runSchemeOfTermEvaluation tops idx_env (CT_Let (g, fvs) (is_rec, defns) body)
    = do
        let n = length defns
            idx_env' = replicate n LI_dummy ++ idx_env
        if is_rec
            then do
                tell [GI_alloc n]
                sequence
                    [ case length params of
                        0 -> do
                            runSchemeOfTermConstruction tops idx_env' rhs
                            tell [GI_update (n - 1 - i)]
                            return ()
                        arity -> do
                            tell [GI_alloc arity]
                            runSchemeOfTermConstruction tops (map LI_var params ++ idx_env') rhs
                            tell (replicate arity GI_mk_abs)
                            tell [GI_update (n - 1 - i)]
                            return ()
                    | (i, (var, (params, rhs))) <- zip [0, 1 .. n - 1] defns
                    ]
                return ()
            else do
                sequence
                    [ case length params of
                        0 -> do
                            runSchemeOfTermConstruction tops (replicate i LI_dummy ++ idx_env) rhs
                            return ()
                        arity -> do
                            tell [GI_alloc arity]
                            runSchemeOfTermConstruction tops (map LI_var params ++ replicate i LI_dummy ++ idx_env) rhs
                            tell (replicate arity GI_mk_abs)
                            return ()
                    | (i, (var, (params, rhs))) <- zip [0, 1 .. n - 1] defns
                    ]
                return ()
        runSchemeOfTermEvaluation tops idx_env' body
        tell [GI_slide n]
        return ()
runSchemeOfTermEvaluation tops idx_env (CT_Mat (g, fvs) body altns)
    = do
        runSchemeOfTermEvaluation tops idx_env body
        tagged_code <- sequence
            [ do
                let arity = length params
                (_, code) <- lift (runWriterT (runSchemeOfTermEvaluation tops (map LI_var params ++ idx_env) rhs))
                tell [GI_slide arity]
                return ((tag, arity), code)
            | (tag, (params, rhs)) <- altns
            ]
        tell [GI_jump tagged_code]
        return ()
runSchemeOfTermEvaluation tops idx_env (CT_Lam (g, fvs) (params, body))
    = case length params of
        0 -> do
            runSchemeOfTermEvaluation tops idx_env body
            return ()
        arity -> do
            tell [GI_alloc arity]
            runSchemeOfTermConstruction tops (map LI_var params ++ idx_env) body
            tell (replicate arity GI_mk_abs)
            return ()

runSchemeOfSupercombinator :: CoreTops IVar (GuaranteeIVarRenamed, FreeVars) -> FunAdr -> CoreAbsn IVar (GuaranteeIVarRenamed, FreeVars) -> StateT Compiler (ExceptT CompileErr Identity) ()
runSchemeOfSupercombinator tops fun_adr (params, rhs) = do
    code' <- case length params of
        0 -> do
            (_, code) <- runWriterT (runSchemeOfTermConstruction tops [] rhs)
            compiler <- get
            let global_idx = Map.size (lookGlobalIdx compiler)
            put (compiler { lookGlobalIdx = Map.insert fun_adr global_idx (lookGlobalIdx compiler), writeInitCode = writeInitCode compiler ++ code ++ [GI_install_gbl] })
            return [GI_push_gbl global_idx]
        arity -> do
            (_, code) <- runWriterT (runSchemeOfTermEvaluation tops (map LI_var params) rhs)
            return (code ++ [GI_update arity, GI_pop arity])
    compiler' <- get
    put (compiler' { findCodeByAdr = Map.insert fun_adr code' (findCodeByAdr compiler') })
    return ()

compileSupercombinator :: CoreTops IVar (GuaranteeIVarRenamed, FreeVars) -> SC -> StateT Compiler (ExceptT CompileErr Identity) (FunAdr, Arity)
compileSupercombinator tops fun = do
    compiler <- get
    case Map.lookup fun (getFunAdrOfSC compiler) of
        Nothing -> case lookup fun tops of
            Nothing -> lift (throwE (CE_cannot_find_top fun))
            Just (params, rhs) -> do
                let fun_adr = getNextFunAdr compiler
                    arity = length params
                put (compiler { getNextFunAdr = fun_adr + 1, getFunAdrOfSC = Map.insert fun (fun_adr, arity) (getFunAdrOfSC compiler) })
                runSchemeOfSupercombinator tops fun_adr (params, rhs)
                return (fun_adr, arity)
        Just (fun_adr, arity) -> return (fun_adr, arity)

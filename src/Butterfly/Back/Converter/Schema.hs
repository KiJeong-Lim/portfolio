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
    constructTerm :: VarIdxEnv -> CoreTerm IVar (GuaranteeIVarRenamed, FreeVars) -> WriterT GmCode (StateT Converter (ExceptT ConvertErr Identity)) ()
    constructTerm env (CT_Var (g, fvs) var)
        = case VI_var var `List.elemIndex` env of
            Nothing -> do
                fun_adr <- lift $ StateT $ flip catchE (const (throwE (CannotFindVar var env))) . runStateT (compileSC var)
                tell [GI_mk_fun fun_adr]
                return ()
            Just idx -> do
                tell [GI_mk_var idx]
                return ()
    constructTerm env (CT_Con (g, fvs) tag)
        = do
            tell [GI_mk_con tag]
            return ()
    constructTerm env (CT_App (g, fvs) term1 term2)
        = do
            constructTerm env term2
            constructTerm (VI_dummy : env) term1
            tell [GI_mk_app]
            return ()
    constructTerm env (CT_Let (g, fvs) (is_rec, defns) body)
        | is_rec = do
            tell [GI_alloc n]
            sequence
                [ do
                    constructTerm env' rhs
                    tell [GI_update (n - i)]
                    return ()
                | (i, (var, (params, rhs))) <- zip [1, 2 .. n] defns
                ]
            constructTerm env' body
            tell [GI_slide n]
            return ()
        | otherwise = do
            sequence
                [ constructTerm (replicate i VI_dummy ++ env) rhs
                | (i, (var, (params, rhs))) <- zip [0, 1 .. n - 1] defns
                ]
            constructTerm env' body
            tell [GI_slide n]
            return ()
        where
            n :: Int
            n = length defns
            env' :: VarIdxEnv
            env' = map (VI_var . fst) defns ++ env
    constructTerm env (CT_Mat (g, fvs) body altns)
        = do
            let args = Set.toList fvs
            code <- lift (constructSC (args, CT_Mat (g, fvs) body altns))
            converter0 <- lift get
            let fun_adr = getAdrForNextSC converter0
            lift (put (converter0 { getAdrForNextSC = fun_adr + 1, bindsGmCodeToSC = Map.insert fun_adr code (bindsGmCodeToSC converter0) }))
            tell [GI_mk_fun fun_adr]
            sequence
                [ case VI_var var `List.elemIndex` (VI_dummy : env) of
                    Just idx -> do
                        tell [GI_mk_var idx]
                        tell [GI_mk_app]
                        return ()
                | var <- args
                ]
            return ()
    constructTerm env (CT_Lam (g, fvs) (params, body))
        | null params = do
            constructTerm env body
            return ()
        | otherwise = do
            let n = length params
            tell [GI_alloc n]
            constructTerm (map VI_var params ++ env) body
            tell (replicate n GI_mk_lam)
            return ()
    evaluateTerm :: VarIdxEnv -> CoreTerm IVar (GuaranteeIVarRenamed, FreeVars) -> WriterT GmCode (StateT Converter (ExceptT ConvertErr Identity)) ()
    evaluateTerm env (CT_Var (g, fvs) var)
        = case VI_var var `List.elemIndex` env of
            Nothing -> do
                fun_adr <- lift $ StateT $ flip catchE (const (throwE (CannotFindVar var env))) . runStateT (compileSC var)
                tell [GI_mk_fun fun_adr, GI_eval]
                return ()
            Just idx -> do
                tell [GI_mk_var idx, GI_eval]
                return ()
    evaluateTerm env (CT_Con (g, fvs) tag)
        = do
            tell [GI_mk_con tag]
            return ()
    evaluateTerm env (CT_App (g, fvs) term1 term2)
        = do
            constructTerm env term2
            constructTerm (VI_dummy : env) term1
            tell [GI_mk_app, GI_eval]
            return ()
    evaluateTerm env (CT_Let (g, fvs) (is_rec, defns) body)
        | is_rec = do
            tell [GI_alloc n]
            sequence
                [ do
                    constructTerm env' rhs
                    tell [GI_update (n - i)]
                    return ()
                | (i, (var, (params, rhs))) <- zip [1, 2 .. n] defns
                ]
            evaluateTerm env' body
            tell [GI_slide n]
            return ()
        | otherwise = do
            sequence
                [ constructTerm (replicate i VI_dummy ++ env) rhs
                | (i, (var, (params, rhs))) <- zip [0, 1 .. n - 1] defns
                ]
            evaluateTerm env' body
            tell [GI_slide n]
            return ()
        where
            n :: Int
            n = length defns
            env' :: VarIdxEnv
            env' = map (VI_var . fst) defns ++ env
    evaluateTerm env (CT_Mat (g, fvs) body altns)
        = do
            evaluateTerm env body
            tagged_codes <- sequence
                [ do
                    (_, code) <- lift (runWriterT (evaluateTerm (map VI_var params ++ env) rhs))
                    return (tag, code)
                | (tag, (params, rhs)) <- altns
                ]
            tell [GI_jump tagged_codes]
            return ()
    evaluateTerm env (CT_Lam (g, fvs) (params, body))
        | null params = do
            evaluateTerm env body
            return ()
        | otherwise = do
            let n = length params
            tell [GI_alloc n]
            constructTerm (map VI_var params ++ env) body
            tell (replicate n GI_mk_lam)
            return ()
    constructSC :: CoreAbsn IVar (GuaranteeIVarRenamed, FreeVars) -> StateT Converter (ExceptT ConvertErr Identity) GmCode
    constructSC (params, rhs) = do
        let d = length params
            env = map VI_var params
        (_, code) <- runWriterT (evaluateTerm env rhs)
        return (code ++ [GI_update d, GI_pop d])
    compileSC :: SC -> StateT Converter (ExceptT ConvertErr Identity) AdrOfSC
    compileSC var = case lookup var tops of
        Nothing -> lift (throwE (CannotFindSC var))
        Just (params, rhs) -> do
            converter0 <- get
            case Map.lookup var (getAdrOfNamedSC converter0) of
                Nothing -> do
                    let fun_adr = getAdrForNextSC converter0
                    put (converter0 { getAdrForNextSC = fun_adr + 1, getAdrOfNamedSC = Map.insert var fun_adr (getAdrOfNamedSC converter0) })
                    code <- constructSC (params, rhs)
                    converter1 <- get
                    put (converter1 { bindsGmCodeToSC = Map.insert fun_adr code (bindsGmCodeToSC converter1) })
                    return fun_adr
                Just fun_adr -> return fun_adr

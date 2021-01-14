module Aladdin.Front.Desugarer.Main where

import Aladdin.Front.Analyzer.Grammar
import Aladdin.Front.Desugarer.ForKind
import Aladdin.Front.Desugarer.ForTerm
import Aladdin.Front.Desugarer.ForType
import Aladdin.Front.Header
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

theInitialKindEnv :: KindEnv
theInitialKindEnv = Map.fromList
    [ (TC_Arrow, read "* -> * -> *")
    , (TC_Named "list", read "* -> *")
    , (TC_Named "o", read "*")
    , (TC_Named "char", read "*")
    , (TC_Named "nat", read "*")
    , (TC_Named "string", read "*")
    ]

theInitialTypeEnv :: TypeEnv
theInitialTypeEnv = Map.fromList
    [ (DC_LO LO_if, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_and, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_or, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_imply, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_sigma, Forall ["a"] ((TyVar 0 `mkTyArrow` mkTyO) `mkTyArrow` mkTyO))
    , (DC_LO LO_pi, Forall ["a"] ((TyVar 0 `mkTyArrow` mkTyO) `mkTyArrow` mkTyO))
    , (DC_LO LO_cut, Forall [] (mkTyO))
    , (DC_LO LO_true, Forall [] (mkTyO))
    , (DC_LO LO_fail, Forall [] (mkTyO))
    , (DC_Nil, Forall ["a"] (mkTyList (TyVar 0)))
    , (DC_Cons, Forall ["a"] (TyVar 0 `mkTyArrow` (mkTyList (TyVar 0) `mkTyArrow` mkTyList (TyVar 0))))
    , (DC_Succ, Forall [] (mkTyNat `mkTyArrow` mkTyNat))
    , (DC_Eq, Forall ["a"] (TyVar 0 `mkTyArrow` (TyVar 0 `mkTyArrow` mkTyO)))
    ]

desugarProgram :: GenUniqueM m => KindEnv -> TypeEnv -> [DeclRep] -> ExceptT ErrMsg m (Program (TermExpr DataConstructor SLoc))
desugarProgram kind_env type_env program
    = case makeKindEnv [ (loc, (tcon, krep)) | RKindDecl loc tcon krep <- program ] kind_env of
        Left err_msg -> throwE err_msg
        Right kind_env' -> case makeTypeEnv kind_env' [ (loc, (con, trep)) | RTypeDecl loc con trep <- program ] type_env of
            Left err_msg -> throwE err_msg
            Right type_env' -> do
                facts' <- lift (mapM (fmap fst . flip runStateT Map.empty . desugarTerm) [ fact_rep | RFactDecl _ fact_rep <- program ])
                return (kind_env' `seq` type_env' `seq` facts' `seq` Program { _KindDecls = kind_env', _TypeDecls = type_env', _FactDecls = facts' })

desugarQuery :: GenUniqueM m => TermRep -> ExceptT ErrMsg m (TermExpr DataConstructor SLoc, Map.Map LargeId IVar)
desugarQuery query0 = runStateT (desugarTerm query0) Map.empty

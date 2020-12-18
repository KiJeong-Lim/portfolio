module Aladdin.Front.Desugarer.DsProgram where

import Aladdin.Front.Analyzer.Grammar
import Aladdin.Front.Desugarer.DsHelper
import Aladdin.Front.Header
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique

desugarProgram :: KindEnv -> TypeEnv -> [Decl] -> ExceptT ErrMsg IO (ModuleBody (TermExpr LargeId SLoc))
desugarProgram kind_env type_env program = do
    kind_env' <- makeKindEnv [ (loc, (tcon, krep)) | KindDecl loc tcon krep <- program ] kind_env
    type_env' <- makeTypeEnv kind_env' [ (loc, (con, trep)) | TypeDecl loc con trep <- program ] type_env
    facts <- mapM (fmap fst . flip runStateT Map.empty . desugarTerm) [ fact_rep | FactDecl _ fact_rep <- program ]
    return (kind_env' `seq` type_env' `seq` facts `seq` ModuleBody { _KindDecls = kind_env', _TypeDecls = type_env', _FactDecls = facts })

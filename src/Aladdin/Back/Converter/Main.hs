module Aladdin.Back.Converter.Main where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Converter.Scheme
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

convertProgram :: GenUniqueM m => Map.Map MetaTVar SmallId -> Map.Map IVar (MonoType Int) -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertProgram used_mtvs assumptions = fmap makeUniversalClosure . convertWithChecking Map.empty initialEnv "fact" where
    initialEnv :: DeBruijnIndicesEnv
    initialEnv = Set.toList (Map.keysSet assumptions) ++ Set.toList (Map.keysSet used_mtvs)
    makeUniversalClosure :: TermNode -> TermNode
    makeUniversalClosure = flip (foldr (\_ -> \term -> (mkNApp (mkNCon LO_ty_pi)) (mkNAbs term))) [1, 2 .. Map.size used_mtvs] . flip (foldr (\_ -> \term -> mkNApp (mkNCon LO_pi) (mkNAbs term))) [1, 2 .. Map.size assumptions]

convertQuery :: GenUniqueM m => Map.Map MetaTVar SmallId -> Map.Map IVar (MonoType Int) -> FreeVariableEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertQuery used_mtvs assumptions var_name_env query
    | Map.null used_mtvs = convertWithChecking var_name_env [] "query" query
    | otherwise = throwE ("converting-error[" ++ pprint 0 (fst (getAnnot query)) ("]:\n  ? query must have no free type variables.\n"))

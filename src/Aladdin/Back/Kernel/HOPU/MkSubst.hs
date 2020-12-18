module Aladdin.Back.Kernel.HOPU.MkSubst where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Disagreement
import Aladdin.Back.Kernel.HOPU.Bind
import Aladdin.Back.Kernel.HOPU.Select
import Aladdin.Back.Kernel.HOPU.Util
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique

mksubst :: LogicVar -> TermNode -> [TermNode] -> Labeling -> ExceptT HopuFail IO (Maybe HopuSol)
mksubst var rhs parameters labeling = catchE (Just . uncurry (flip HopuSol) <$> runStateT (go var (rewrite HNF rhs) parameters) labeling) handleErr where
    go :: LogicVar -> TermNode -> [TermNode] -> StateT Labeling (ExceptT HopuFail IO) LVarSubst
    go var rhs parameters
        | (lambda, rhs') <- viewNestedNAbs rhs
        , (LVar var', rhs_tail) <- unfoldlNApp rhs'
        , var == var'
        = do
            labeling <- get
            let isty = isTypeLVar var
                n = length parameters + lambda
                lhs_arguments = [ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda, lambda - 1 .. 1] 
                rhs_arguments = map (rewrite NF) rhs_tail
                common_arguments = [ mkNIdx (n - i) | i <- [0, 1 .. n - 1], lhs_arguments !! i == rhs_arguments !! i ]
            if isPatternRespectTo var' rhs_arguments labeling
                then do
                    common_head <- getNewLVar isty (lookupLabel var labeling)
                    case var' +-> makeNestedNAbs n (foldlNApp common_head common_arguments) of
                        Nothing -> lift (throwE OccursCheckFail)
                        Just theta -> do
                            modify (zonkLVar theta)
                            return theta
                else lift (throwE NotAPattern)
        | otherwise
        = do
            labeling <- get
            let n = length parameters
                lhs_arguments = map (rewrite NF) parameters
            if isPatternRespectTo var lhs_arguments labeling
                then do
                    (subst, lhs) <- bind var rhs parameters 0
                    case var +-> makeNestedNAbs n lhs of
                        Nothing -> lift (throwE OccursCheckFail)
                        Just theta -> do
                            modify (zonkLVar theta)
                            return (theta <> subst)
                else lift (throwE NotAPattern)
    handleErr :: HopuFail -> ExceptT HopuFail IO (Maybe HopuSol)
    handleErr NotAPattern = return Nothing
    handleErr err = throwE err

module Aladdin.Back.HOPU.MkSubst where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.HOPU.Bind
import Aladdin.Back.HOPU.Select
import Aladdin.Back.HOPU.Util
import Aladdin.Front.Header
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict

mksubst :: GenUniqueM m => LogicVar -> TermNode -> [TermNode] -> Labeling -> ExceptT HopuFail m (Maybe HopuSol)
mksubst var rhs parameters labeling = catchE (Just . uncurry (flip HopuSol) <$> runStateT (go var (rewrite HNF rhs) parameters) labeling) handleErr where
    go :: GenUniqueM m => LogicVar -> TermNode -> [TermNode] -> StateT Labeling (ExceptT HopuFail m) LVarSubst
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
    handleErr :: GenUniqueM m => HopuFail -> ExceptT HopuFail m (Maybe HopuSol)
    handleErr NotAPattern = return Nothing
    handleErr err = throwE err

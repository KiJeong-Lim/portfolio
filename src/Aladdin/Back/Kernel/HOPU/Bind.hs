module Aladdin.Back.Kernel.HOPU.Bind where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Disagreement
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

bind :: LogicVar -> TermNode -> [TermNode] -> Int -> StateT Labeling (ExceptT HopuFail IO) (LVarSubst, TermNode)
bind var = go . rewrite HNF where
    go :: TermNode -> [TermNode] -> Int -> StateT Labeling (ExceptT HopuFail IO) (LVarSubst, TermNode)
    go rhs parameters lambda
        | (lambda', rhs') <- viewNestedNAbs rhs
        , lambda' > 0
        = do
            (subst, lhs') <- go rhs' parameters (lambda + lambda')
            return (subst, makeNestedNAbs lambda' lhs')
        | (rhs_head, rhs_tail) <- unfoldlNApp rhs
        , isRigid rhs_head
        = do
            labeling <- get
            let loop [] = return (mempty, [])
                loop (rhs_tail_elements : rhs_tail) = do
                    (subst, lhs_tail_elements) <- go (rewrite HNF rhs_tail_elements) parameters lambda
                    (theta, lhs_tail) <- loop (applyBinding subst rhs_tail)
                    return (theta <> subst, lhs_tail_elements : lhs_tail)
                get_lhs_head lhs_arguments
                    | NCon con <- rhs_head
                    , lookupLabel var labeling >= lookupLabel con labeling
                    = return rhs_head
                    | Just idx <- rhs_head `List.elemIndex` lhs_arguments
                    = return (mkNIdx (length lhs_arguments - idx))
                    | otherwise
                    = lift (throwE FlexRigidFail)
            lhs_head <- get_lhs_head ([ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda, lambda - 1 .. 1])
            (subst, lhs_tail) <- loop rhs_tail
            return (subst, foldlNApp lhs_head lhs_tail)
        | (LVar var', rhs_tail) <- unfoldlNApp rhs
        = if var == var'
            then lift (throwE OccursCheckFail)
            else do
                labeling <- get
                let isty = isTypeLVar var
                    lhs_arguments = [ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda, lambda - 1 .. 1]
                    rhs_arguments = map (rewrite NF) rhs_tail
                    common_arguments = Set.toList (Set.fromList lhs_arguments `Set.intersection` Set.fromList rhs_arguments)
                if isPatternRespectTo var' rhs_arguments labeling
                    then do
                        (lhs_inner, rhs_inner) <- case lookupLabel var labeling `compare` lookupLabel var' labeling of
                            LT -> do
                                selected_rhs_parameters <- lhs_arguments `up` var'
                                selected_lhs_parameters <- selected_rhs_parameters`down` lhs_arguments
                                return (selected_lhs_parameters, selected_rhs_parameters)
                            geq -> do
                                selected_lhs_parameters <- rhs_arguments `up` var
                                selected_rhs_parameters <- selected_lhs_parameters `down` rhs_arguments
                                return (selected_lhs_parameters, selected_rhs_parameters)
                        lhs_outer <- common_arguments `down` lhs_arguments
                        rhs_outer <- common_arguments `down` rhs_arguments
                        common_head <- getNewLVar isty (lookupLabel var labeling)
                        case var' +-> makeNestedNAbs (length rhs_tail) (foldlNApp common_head (rhs_inner ++ rhs_outer)) of
                            Nothing -> lift (throwE OccursCheckFail)
                            Just theta -> do
                                modify (zonkLVar theta)
                                return (theta, foldlNApp common_head (lhs_inner ++ lhs_outer))
                    else lift (throwE NotAPattern)
        | otherwise
        = lift (throwE BindFail)

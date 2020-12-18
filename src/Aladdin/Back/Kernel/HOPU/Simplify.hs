module Aladdin.Back.Kernel.HOPU.Simplify where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Disagreement
import Aladdin.Back.Kernel.HOPU.Bind
import Aladdin.Back.Kernel.HOPU.MkSubst
import Aladdin.Back.Kernel.HOPU.Select
import Aladdin.Back.Kernel.HOPU.Util
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique

type HasChanged = Bool

simplify :: IORef HasChanged -> [Disagreement] -> Labeling -> ExceptT HopuFail IO ([Disagreement], HopuSol)
simplify changed = flip loop mempty where
    loop :: [Disagreement] -> LVarSubst -> Labeling -> ExceptT HopuFail IO ([Disagreement], HopuSol)
    loop [] subst labeling = return ([], HopuSol labeling subst)
    loop (lhs :=?=: rhs : disagreements) subst labeling = go (rewrite HNF lhs) (rewrite HNF rhs) where
        go :: TermNode -> TermNode -> ExceptT HopuFail IO ([Disagreement], HopuSol)
        go lhs rhs
            | (lambda1, lhs') <- viewNestedNAbs lhs
            , (lambda2, rhs') <- viewNestedNAbs rhs
            , lambda1 > 0 && lambda2 > 0
            = case lambda1 `compare` lambda2 of
                LT -> go lhs' (makeNestedNAbs (lambda2 - lambda1) rhs')
                EQ -> go lhs' rhs'
                GT -> go (makeNestedNAbs (lambda1 - lambda2) lhs') rhs'
            | (lambda1, lhs') <- viewNestedNAbs lhs
            , (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , lambda1 > 0 && isRigid rhs_head
            = go lhs' (foldlNApp (rewriteWithSusp rhs_head 0 lambda1 [] HNF) ([ mkSusp rhs_tail_element 0 lambda1 [] | rhs_tail_element <- rhs_tail ] ++ map mkNIdx [lambda1, lambda1 - 1 .. 1]))
            | (lhs_head, lhs_tail) <- unfoldlNApp lhs
            , (lambda2, rhs') <- viewNestedNAbs rhs
            , isRigid lhs_head && lambda2 > 0
            = go (foldlNApp (rewriteWithSusp lhs_head 0 lambda2 [] HNF) ([ mkSusp lhs_tail_element 0 lambda2 [] | lhs_tail_element <- lhs_tail ] ++ map mkNIdx [lambda2, lambda2 - 1 .. 1])) rhs'
            | (lhs_head, lhs_tail) <- unfoldlNApp lhs
            , (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , isRigid lhs_head && isRigid rhs_head
            = if lhs_head == rhs_head && length lhs_tail == length rhs_tail
                then loop ([ lhs' :=?=: rhs' | (lhs', rhs') <- zip lhs_tail rhs_tail ] ++ disagreements) subst labeling
                else throwE RigidRigidFail
            | (LVar var, parameters) <- unfoldlNApp lhs
            = do
                output <- mksubst var rhs parameters labeling
                case output of
                    Nothing -> solveNext
                    Just (HopuSol labeling' subst') -> do
                        liftIO (writeIORef changed True)
                        loop (applyBinding subst' disagreements) (subst' <> subst) labeling'
            | (LVar var, parameters) <- unfoldlNApp rhs
            = do
                output <- mksubst var lhs parameters labeling
                case output of
                    Nothing -> solveNext
                    Just (HopuSol labeling' subst') -> do
                        liftIO (writeIORef changed True)
                        loop (applyBinding subst' disagreements) (subst' <> subst) labeling'
            | otherwise
            = solveNext
        solveNext :: ExceptT HopuFail IO ([Disagreement], HopuSol)
        solveNext = do
            (disagreements', HopuSol labeling' subst') <- loop disagreements mempty labeling
            return (applyBinding subst' (lhs :=?=: rhs) : disagreements', HopuSol labeling' (subst' <> subst))

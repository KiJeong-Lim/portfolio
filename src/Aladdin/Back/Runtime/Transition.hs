module Aladdin.Back.Runtime.Transition where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.HOPU.Main
import Aladdin.Back.HOPU.Util
import Aladdin.Back.Runtime.Instantiation
import Aladdin.Back.Runtime.LogicalOperator
import Aladdin.Back.Runtime.Util
import Aladdin.Front.Header
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

runTransition :: RuntimeEnv -> Set.Set LogicVar -> Stack -> [Stack] -> ExceptT KernelErr (UniqueGenT IO) Satisfied
runTransition env free_lvars = go where
    failure :: ExceptT KernelErr (UniqueGenT IO) Stack
    failure = return []
    success :: (Context, [Cell]) -> ExceptT KernelErr (UniqueGenT IO) Stack
    success with = return [with]
    search :: [Fact] -> ScopeLevel -> Constant -> [TermNode] -> Context -> [Cell] -> ExceptT KernelErr (UniqueGenT IO) Stack
    search facts level pred args ctx cells
        = fmap concat $ forM facts $ \fact -> do
            ((goal', new_goal), labeling) <- runStateT (instantiateFact fact level) (_CurrentLabeling ctx)
            case unfoldlNApp (rewrite HNF goal') of
                (NCon pred', args')
                    | pred == pred' -> do
                        hopu_ouput <- if length args == length args'
                            then lift (runHOPU labeling (zipWith (:=?=:) args args' ++ _LeftConstraints ctx))
                            else throwE (BadFactGiven goal')
                        let new_level = level
                            new_facts = facts
                        case hopu_ouput of
                            Nothing -> failure
                            Just (new_disagreements, HopuSol new_labeling subst) -> success
                                ( Context
                                    { _TotalVarBinding = zonkLVar subst (_TotalVarBinding ctx)
                                    , _CurrentLabeling = new_labeling
                                    , _LeftConstraints = new_disagreements
                                    }
                                , zonkLVar subst (mkCell new_facts new_level new_goal : cells)
                                )
                _ -> failure
    dispatch :: Context -> [Fact] -> ScopeLevel -> (TermNode, [TermNode]) -> [Cell] -> Stack -> [Stack] -> ExceptT KernelErr (UniqueGenT IO) Satisfied
    dispatch ctx facts level (NCon pred, args) cells stack stacks
        | DC (DC_LO logical_operator) <- pred
        = do
            stack' <- runLogicalOperator logical_operator args ctx facts level cells stack
            go stack' stacks
        | otherwise
        = do
            stack' <- search facts level pred args ctx cells
            go stack' (stack : stacks)
    dispatch ctx facts level (t, ts) cells stack stacks = throwE (BadGoalGiven (foldlNApp t ts))
    go :: Stack -> [Stack] -> ExceptT KernelErr (UniqueGenT IO) Satisfied
    go [] [] = return False
    go [] (stack : stacks) = go stack stacks
    go ((ctx, cells) : stack) stacks = do
        liftIO (_PutStr env (showsCurrentState free_lvars ctx cells stack ""))
        case cells of
            [] -> do
                want_more <- liftIO (_Answer env ctx)
                if want_more then go stack stacks else return True
            Cell facts level goal : cells' -> dispatch ctx facts level (unfoldlNApp (rewrite HNF goal)) cells' stack stacks

module Aladdin.Back.Kernel.Runtime.Transition where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Disagreement
import Aladdin.Back.Kernel.HOPU
import Aladdin.Back.Kernel.HOPU.Util
import Aladdin.Back.Kernel.KernelErr
import Aladdin.Back.Kernel.Runtime.Instantiation
import Aladdin.Back.Kernel.Runtime.LogicalOperator
import Aladdin.Back.Kernel.Runtime.Util
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict

runTransition :: RuntimeEnv -> Stack -> [Stack] -> ExceptT KernelErr IO Satisfied
runTransition env = go where
    failure :: ExceptT KernelErr IO Stack
    failure = return []
    success :: (Context, [Cell]) -> ExceptT KernelErr IO Stack
    success with = return [with]
    search :: [Fact] -> ScopeLevel -> DataConstructor -> [TermNode] -> Context -> [Cell] -> ExceptT KernelErr IO Stack
    search facts level pred args ctx cells
        = fmap concat $ forM facts $ \fact -> do
            ((goal', new_goal), labeling) <- runStateT (instantiateFact fact level) (_CurrentLabeling ctx)
            case unfoldlNApp (rewrite HNF goal') of
                (NCon (DC pred'), args')
                    | pred == pred' -> do
                        hopu_ouput <- if length args == length args'
                            then liftIO (runHOPU labeling (zipWith (:=?=:) args args' ++ _LeftConstraints ctx))
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
    dispatch :: Context -> [Fact] -> ScopeLevel -> (TermNode, [TermNode]) -> [Cell] -> Stack -> [Stack] -> ExceptT KernelErr IO Satisfied
    dispatch ctx facts level (NCon key, args) cells stack stacks
        | LO logical_operator <- key
        = do
            stack' <- runLogicalOperator logical_operator args ctx facts level cells stack
            go stack' stacks
        | DC DC_eq <- key
        = case args of
            [typ, lhs, rhs] -> do
                hopu_ouput <- liftIO (runHOPU (_CurrentLabeling ctx) (lhs :=?=: rhs : _LeftConstraints ctx))
                stack' <- case hopu_ouput of
                    Nothing -> failure
                    Just (new_disagreements, HopuSol new_labeling subst) -> success
                        ( Context
                            { _TotalVarBinding = zonkLVar subst (_TotalVarBinding ctx)
                            , _CurrentLabeling = new_labeling
                            , _LeftConstraints = new_disagreements
                            }
                        , zonkLVar subst cells
                        )
                go (stack' ++ stack) stacks
            _ -> throwE (BadGoalGiven (foldlNApp (mkNCon key) args))
        | DC pred <- key
        = do
            stack' <- search facts level pred args ctx cells
            go stack' (stack : stacks)
    dispatch ctx facts level (t, ts) cells stack stacks = throwE (BadGoalGiven (foldlNApp t ts))
    go :: Stack -> [Stack] -> ExceptT KernelErr IO Satisfied
    go [] [] = return False
    go [] (stack : stacks) = go stack stacks
    go ((ctx, cells) : stack) stacks = do
        liftIO (_PutStr env (showsCurrentState ctx cells stack ""))
        case cells of
            [] -> do
                want_more <- liftIO (_Answer env ctx)
                if want_more then go stack stacks else return True
            Cell facts level goal : cells' -> dispatch ctx facts level (unfoldlNApp (rewrite HNF goal)) cells' stack stacks

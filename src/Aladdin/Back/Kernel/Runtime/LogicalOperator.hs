module Aladdin.Back.Kernel.Runtime.LogicalOperator where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.KernelErr
import Aladdin.Back.Kernel.Runtime.Util
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Unique

runLogicalOperator :: LogicalOperator -> [TermNode] -> Context -> [Fact] -> ScopeLevel -> [Cell] -> Stack -> ExceptT KernelErr IO Stack
runLogicalOperator LO_true [] ctx facts level cells stack
    = return ((ctx, cells) : stack)
runLogicalOperator LO_fail [] ctx facts level cells stack
    = return stack
runLogicalOperator LO_cut [] ctx facts level cells stack
    = return [(ctx, cells)]
runLogicalOperator LO_and [goal1, goal2] ctx facts level cells stack
    = return ((ctx, mkCell facts level goal1 : mkCell facts level goal2 : cells) : stack)
runLogicalOperator LO_or [goal1, goal2] ctx facts level cells stack
    = return ((ctx, mkCell facts level goal1 : cells) : (ctx, mkCell facts level goal2 : cells) : stack)
runLogicalOperator LO_imply [fact1, goal2] ctx facts level cells stack
    = return ((ctx, mkCell (fact1 : facts) level goal2 : cells) : stack)
runLogicalOperator LO_sigma [goal1] ctx facts level cells stack
    = do
        uni <- liftIO newUnique
        let var = LV_Unique uni
        return ((ctx { _CurrentLabeling = enrollLabel var level (_CurrentLabeling ctx) }, mkCell facts level (mkNApp goal1 (mkLVar var)) : cells) : stack)
runLogicalOperator LO_pi [goal1] ctx facts level cells stack
    = do
        uni <- liftIO newUnique
        let con = DC (DC_Unique uni)
        return ((ctx { _CurrentLabeling = enrollLabel con (level + 1) (_CurrentLabeling ctx) }, mkCell facts (level + 1) (mkNApp goal1 (mkNCon con)) : cells) : stack)
runLogicalOperator logical_operator args ctx facts level cells stack
    = throwE (BadGoalGiven (foldlNApp (mkNCon logical_operator) args))

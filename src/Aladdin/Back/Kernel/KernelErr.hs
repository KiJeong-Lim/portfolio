module Aladdin.Back.Kernel.KernelErr where

import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Show
import Lib.Base

data KernelErr
    = BadGoalGiven TermNode
    | BadFactGiven TermNode
    deriving ()

module Butterfly.Back.Executor.Transition where

import Butterfly.Back.Base.Instruction
import Butterfly.Back.Base.Util
import Butterfly.Back.Executor.Util
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

runTransition :: GmCode -> GmStack -> GmDummy -> StateT Executor (ExceptT RuntimeErr IO) ()
runTransition = undefined

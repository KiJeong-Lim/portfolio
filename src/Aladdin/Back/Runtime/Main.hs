module Aladdin.Back.Runtime.Main where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Runtime.Transition
import Aladdin.Back.Runtime.Util
import Aladdin.Front.Header
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

execRuntime :: RuntimeEnv -> [Fact] -> Goal -> ExceptT KernelErr (UniqueGenT IO) Satisfied
execRuntime env program query = runTransition env [(initialContext, [mkCell program 0 query])] [] where
    initialContext :: Context
    initialContext = Context
        { _TotalVarBinding = mempty
        , _CurrentLabeling = Labeling
            { _ConLabel = Map.empty
            , _VarLabel = Map.fromSet (const 0) (getFreeLVs query)
            }
        , _LeftConstraints = []
        }

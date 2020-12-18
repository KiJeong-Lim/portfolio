module Aladdin.Front.Desugarer.DsQuery where

import Aladdin.Front.Analyzer.Grammar
import Aladdin.Front.Desugarer.DsHelper
import Aladdin.Front.Header
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique

desugarQuery :: TermRep -> ExceptT ErrMsg IO (TermExpr LargeId SLoc, Map.Map SmallId IVar)
desugarQuery query0 = runStateT (desugarTerm query0) Map.empty

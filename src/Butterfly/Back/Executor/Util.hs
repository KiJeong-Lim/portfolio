module Butterfly.Back.Executor.Util where

import Butterfly.Back.Base.Instruction
import Butterfly.Back.Base.Util
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

type GmStack = [AdrOf TermNode]

type GmDummy = [(GmStack, GmCode)]

data TermNode
    = NPtr (AdrOf TermNode)
    | NCon Tag
    | NFun (AdrOf SC) Arity
    | NApp (AdrOf TermNode) (AdrOf TermNode)
    | NAbs (AdrOf TermNode) (AdrOf TermNode)
    deriving (Eq)

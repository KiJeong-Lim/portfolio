module Butterfly.Back.Converter.Util where

import Butterfly.Back.Base.CoreTerm
import Butterfly.Back.Base.Instruction
import Butterfly.Back.Base.Util
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

type VarIdxEnv = [VarIdxEnvItem]

data VarIdxEnvItem
    = VI_local IVar
    | VI_dummy
    deriving (Eq)

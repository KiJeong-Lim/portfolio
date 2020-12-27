module Butterfly.Back.Compiler.Util where

import Butterfly.Back.Base.CoreTerm
import Butterfly.Back.Base.Instruction
import Butterfly.Back.Base.Util
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

type LocalIdxEnv = [LocalIdxEnvItem]

type GlobalIdxEnv = Map.Map FunAdr GlobalIdx

data LocalIdxEnvItem
    = LI_var IVar
    | LI_dummy
    deriving (Eq)

data Compiler
    = Compiler
        { getFunAdrOfSC :: Map.Map SC (FunAdr, Arity)
        , getNextFunAdr :: AdrOf GmCode
        , findCodeByAdr :: Map.Map FunAdr GmCode
        , lookGlobalIdx :: GlobalIdxEnv
        , writeInitCode :: GmCode
        }
    deriving ()

data CompileErr
    = CE_cannot_find_var IVar LocalIdxEnv
    | CE_cannot_find_top SC
    deriving ()

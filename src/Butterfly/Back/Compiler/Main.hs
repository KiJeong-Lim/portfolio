module Butterfly.Back.Compiler.Main where

import Butterfly.Back.Base.CoreTerm
import Butterfly.Back.Base.Instruction
import Butterfly.Back.Base.Util
import Butterfly.Back.Compiler.Util
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

compileProgram :: Compiler -> CoreTops IVar (GuaranteeIVarRenamed, FreeVars) -> ExceptT CompileErr Identity Compiler
compileProgram = undefined

compileQuery :: Compiler -> CoreTerm IVar (GuaranteeIVarRenamed, FreeVars) -> ExceptT CompileErr Identity GmCode
compileQuery = undefined

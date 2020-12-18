module Aladdin.Back.Kernel.Runtime.Instantiation where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Kernel.KernelErr
import Aladdin.Back.Kernel.Runtime.Util
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Unique

instantiateFact :: Fact -> ScopeLevel -> StateT Labeling (ExceptT KernelErr IO) (TermNode, TermNode)
instantiateFact fact level
    = case unfoldlNApp (rewrite HNF fact) of
        (NCon (LO LO_ty_pi), [fact1]) -> do
            uni <- liftIO newUnique
            let var = LV_ty_var uni
            modify (enrollLabel var level)
            instantiateFact (mkNApp fact1 (mkLVar var)) level
        (NCon (LO LO_pi), [fact1]) -> do
            uni <- liftIO newUnique
            let var = LV_Unique uni
            modify (enrollLabel var level)
            instantiateFact (mkNApp fact1 (mkLVar var)) level
        (NCon (LO LO_if), [conclusion, premise]) -> return (conclusion, premise)
        (NCon (LO logical_operator), args) -> lift (throwE (BadFactGiven (foldlNApp (mkNCon logical_operator) args)))
        (t, ts) -> return (foldlNApp t ts, mkNCon (LO LO_true))

module Aladdin.Back.Kernel.HOPU where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Disagreement
import Aladdin.Back.Kernel.HOPU.Bind
import Aladdin.Back.Kernel.HOPU.MkSubst
import Aladdin.Back.Kernel.HOPU.Select
import Aladdin.Back.Kernel.HOPU.Simplify
import Aladdin.Back.Kernel.HOPU.Util
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef

runHOPU :: Labeling -> [Disagreement] -> IO (Maybe ([Disagreement], HopuSol))
runHOPU = go where
    loop :: IORef HasChanged -> ([Disagreement], HopuSol) -> ExceptT HopuFail IO ([Disagreement], HopuSol)
    loop changed (disagreements, HopuSol labeling subst)
        | null disagreements = return (disagreements, HopuSol labeling subst)
        | otherwise = do
            (disagreements', HopuSol labeling' subst') <- simplify changed disagreements labeling
            let result = (disagreements', HopuSol labeling' (subst' <> subst))
            has_changed <- liftIO (readIORef changed)
            if has_changed
                then do
                    liftIO (writeIORef changed False)
                    loop changed result
                else return result
    go :: Labeling -> [Disagreement] -> IO (Maybe ([Disagreement], HopuSol))
    go labeling disagreements = do
        changed <- newIORef False
        output <- runExceptT (loop changed (disagreements, HopuSol labeling mempty))
        case output of
            Left err -> return Nothing
            Right result -> return (Just result)

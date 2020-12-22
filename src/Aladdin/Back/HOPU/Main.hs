module Aladdin.Back.HOPU.Main where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.HOPU.Bind
import Aladdin.Back.HOPU.MkSubst
import Aladdin.Back.HOPU.Select
import Aladdin.Back.HOPU.Simplify
import Aladdin.Back.HOPU.Util
import Aladdin.Front.Header
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict

runHOPU :: GenUniqueM m => Labeling -> [Disagreement] -> m (Maybe ([Disagreement], HopuSol))
runHOPU = go where
    loop :: GenUniqueM m => ([Disagreement], HopuSol) -> StateT HasChanged (ExceptT HopuFail m) ([Disagreement], HopuSol)
    loop (disagreements, HopuSol labeling subst)
        | null disagreements = return (disagreements, HopuSol labeling subst)
        | otherwise = do
            (disagreements', HopuSol labeling' subst') <- simplify disagreements labeling
            let result = (disagreements', HopuSol labeling' (subst' <> subst))
            has_changed <- get
            if has_changed
                then do
                    put False
                    loop result
                else return result
    go :: GenUniqueM m => Labeling -> [Disagreement] -> m (Maybe ([Disagreement], HopuSol))
    go labeling disagreements = do
        output <- runExceptT (runStateT (loop (disagreements, HopuSol labeling mempty)) False)
        case output of
            Left err -> return Nothing
            Right (result, _) -> return (Just result)

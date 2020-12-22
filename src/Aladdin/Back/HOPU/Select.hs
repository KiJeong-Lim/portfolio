module Aladdin.Back.HOPU.Select where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.HOPU.Util
import Aladdin.Front.Header
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

isRigid :: TermNode -> Bool
isRigid (NCon c) = True
isRigid (NIdx i) = True
isRigid _ = False

areAllDistinct :: Eq a => [a] -> Bool
areAllDistinct [] = True
areAllDistinct (x : xs) = not (elem x xs) && areAllDistinct xs

isPatternRespectTo :: LogicVar -> [TermNode] -> Labeling -> Bool
isPatternRespectTo v ts labeling = and
    [ all isRigid ts
    , areAllDistinct ts
    , and
        [ lookupLabel v labeling < lookupLabel c labeling
        | NCon c <- ts
        ]
    ]

down :: Monad m => [TermNode] -> [TermNode] -> StateT Labeling (ExceptT HopuFail m) [TermNode]
zs `down` ts = if downable then return indices else lift (throwE DownFail) where
    downable :: Bool
    downable = and
        [ areAllDistinct ts
        , all isRigid ts
        , areAllDistinct zs
        , all isRigid zs
        ]
    indices :: [TermNode]
    indices = map mkNIdx
        [ length ts - i
        | z <- zs
        , i <- fromMaybeToList (z `List.elemIndex` ts)
        ]

up :: Monad m => [TermNode] -> LogicVar -> StateT Labeling (ExceptT HopuFail m) [TermNode]
ts `up` y = if upable then fmap findVisibles get else lift (throwE UpFail) where
    upable :: Bool
    upable = and
        [ areAllDistinct ts
        , all isRigid ts
        ]
    findVisibles :: Labeling -> [TermNode]
    findVisibles labeling = map mkNCon
        [ c
        | NCon c <- ts
        , lookupLabel c labeling <= lookupLabel y labeling
        ]

module Butterfly.Back.Converter.Util where

import Butterfly.Back.Base.CoreTerm
import Butterfly.Back.Base.Instruction
import Butterfly.Back.Base.Util
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

data IVarIndexEnv
    = IVarIndexEnv
        { getDepthOfIIE :: Int
        , findIdxOfName :: Map.Map IVar Int
        }
    deriving ()

instance Outputable IVarIndexEnv where
    pprint _ (IVarIndexEnv dep mapsto) = strcat
        [ pindent 4 . strstr "IVarIndexEnv" . nl
        , pindent 6 . strstr "{ getDepthOfIIE = " . showsPrec 0 dep . nl
        , pindent 6 . strstr ", findIdxOfName = " . plist 8 [ showsPrec 0 var . strstr ": " . showsPrec 0 idx | (var, idx) <- Map.toList mapsto ] . nl
        , pindent 6 . strstr "}"
        ]

emptyIIE :: IVarIndexEnv
emptyIIE = IVarIndexEnv { getDepthOfIIE = 0, findIdxOfName = Map.empty }

increaseDepthOfIIE :: Int -> IVarIndexEnv -> IVarIndexEnv
increaseDepthOfIIE n env = env { getDepthOfIIE = n + getDepthOfIIE env }

lookupIIE :: IVar -> IVarIndexEnv -> Either ErrMsg Int
lookupIIE var (IVarIndexEnv dep mapsto) = maybe (Left ("  ? couldn't find the variable " ++ showsPrec 0 var (" in the following environment:\n" ++ pprint 0 (IVarIndexEnv dep mapsto) ""))) (\n -> let idx = dep - n in idx `seq` Right idx) (Map.lookup var mapsto)

insertIIE :: IVar -> IVarIndexEnv -> IVarIndexEnv
insertIIE var (IVarIndexEnv dep mapsto) = case Map.lookup var mapsto of
    Nothing -> let dep' = dep + 1 in dep' `seq` IVarIndexEnv { getDepthOfIIE = dep', findIdxOfName = Map.insert var dep' mapsto }
    Just n -> let dep' = dep + 1 in dep' `seq` IVarIndexEnv { getDepthOfIIE = dep', findIdxOfName = Map.update (const (Just dep')) var mapsto }

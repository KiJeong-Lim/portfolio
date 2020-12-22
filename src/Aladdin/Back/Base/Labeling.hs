module Aladdin.Back.Base.Labeling where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Front.Header
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type ScopeLevel = Int

data Labeling
    = Labeling
        { _ConLabel :: Map.Map Constant ScopeLevel
        , _VarLabel :: Map.Map LogicVar ScopeLevel
        }
    deriving ()

class Labelable atom where
    enrollLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    updateLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    lookupLabel :: atom -> Labeling -> ScopeLevel

instance Labelable Constant where
    enrollLabel atom level labeling = labeling { _ConLabel = Map.insert atom level (_ConLabel labeling) }
    updateLabel atom level labeling = labeling { _ConLabel = Map.update (const (Just level)) atom (_ConLabel labeling) }
    lookupLabel (DC data_constructor) = maybe (theDefaultLevel data_constructor) id . Map.lookup (DC data_constructor) . _ConLabel
    lookupLabel (TC type_constructor) = const 0

instance Labelable LogicVar where
    enrollLabel atom level labeling = labeling { _VarLabel = Map.insert atom level (_VarLabel labeling) }
    updateLabel atom level labeling = labeling { _VarLabel = Map.update (const (Just level)) atom (_VarLabel labeling) }
    lookupLabel atom = maybe maxBound id . Map.lookup atom . _VarLabel

instance ZonkLVar Labeling where
    zonkLVar subst labeling
        = labeling
            { _VarLabel = Map.fromAscList
                [ mkstrict
                    ( v
                    , foldr min (lookupLabel v labeling)
                        [ level'
                        | (v', t') <- Map.toList mapsto
                        , v `Set.member` getFreeLVs t'
                        , level' <- fromMaybeToList (Map.lookup v' varlabel)
                        ]
                    )
                | v <- Set.toAscList (Map.keysSet mapsto `Set.union` Map.keysSet varlabel)
                ]
            }
        where
            mapsto :: Map.Map LogicVar TermNode
            mapsto = unVarBinding subst
            varlabel :: Map.Map LogicVar ScopeLevel
            varlabel = _VarLabel labeling
            mkstrict :: (LogicVar, ScopeLevel) -> (LogicVar, ScopeLevel)
            mkstrict pair = snd pair `seq` pair

fromMaybeToList :: Maybe a -> [a]
fromMaybeToList Nothing = []
fromMaybeToList (Just x) = [x]

theDefaultLevel :: DataConstructor -> ScopeLevel
theDefaultLevel (DC_Unique uni) = maxBound
theDefaultLevel _ = 0

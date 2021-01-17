module Aladdin.Back.Base.VarBinding where

import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

infix 1 +->

type LVarSubst = VarBinding

newtype VarBinding
    = VarBinding { unVarBinding :: Map.Map LogicVar TermNode }
    deriving (Eq)

class HasLVar expr where
    getFreeLVars :: expr -> Set.Set LogicVar -> Set.Set LogicVar
    applyBinding :: VarBinding -> expr -> expr

class ZonkLVar expr where
    zonkLVar :: LVarSubst -> expr -> expr

instance HasLVar TermNode where
    getFreeLVars (LVar v) = Set.insert v
    getFreeLVars (NCon c) = id
    getFreeLVars (NIdx i) = id
    getFreeLVars (NApp t1 t2) = getFreeLVars t1 . getFreeLVars t2
    getFreeLVars (NAbs t) = getFreeLVars t
    getFreeLVars (Susp t ol nl env) = getFreeLVars (rewriteWithSusp t ol nl env HNF)
    applyBinding = flatten

instance HasLVar a => HasLVar [a] where
    getFreeLVars = flip (foldr getFreeLVars)
    applyBinding = map . applyBinding

instance HasLVar b => HasLVar (a, b) where
    getFreeLVars = getFreeLVars . snd
    applyBinding = fmap . applyBinding

instance HasLVar a => HasLVar (Map.Map k a) where
    getFreeLVars = getFreeLVars . Map.elems
    applyBinding = Map.map . applyBinding

instance Semigroup VarBinding where
    theta2 <> theta1 = map21 `seq` VarBinding map21 where
        map1 :: Map.Map LogicVar TermNode
        map1 = unVarBinding theta1
        map2 :: Map.Map LogicVar TermNode
        map2 = unVarBinding theta2
        map21 :: Map.Map LogicVar TermNode
        map21 = applyBinding theta2 map1 `Map.union` map2

instance Monoid VarBinding where
    mempty = map0 `seq` VarBinding map0 where
        map0 :: Map.Map LogicVar TermNode
        map0 = Map.empty

instance ZonkLVar VarBinding where
    zonkLVar subst binding = subst <> binding

instance ZonkLVar a => ZonkLVar [a] where
    zonkLVar = map . zonkLVar

getFreeLVs :: HasLVar expr => expr -> Set.Set LogicVar
getFreeLVs = flip getFreeLVars Set.empty

flatten :: VarBinding -> TermNode -> TermNode
flatten (VarBinding mapsto) = go where
    go :: TermNode -> TermNode
    go (LVar v) = case Map.lookup v mapsto of
        Nothing -> mkLVar v
        Just t -> t
    go (NCon c) = mkNCon c
    go (NIdx i) = mkNIdx i
    go (NApp t1 t2) = mkNApp (go t1) (go t2)
    go (NAbs t) = mkNAbs (go t)
    go (Susp t ol nl env) = mkSusp (go t) ol nl (lensForSuspEnv go env)

(+->) :: LogicVar -> TermNode -> Maybe VarBinding
v +-> t
    | v `Set.member` getFreeLVs t' = Nothing
    | otherwise = return (VarBinding (Map.singleton v t'))
    where
        t' :: TermNode
        t' = rewrite NF t

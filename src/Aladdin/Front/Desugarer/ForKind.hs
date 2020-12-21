module Aladdin.Front.Desugarer.ForKind where

import Aladdin.Front.Analyzer.Grammar
import Aladdin.Front.Header
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

makeKindEnv :: [(SLoc, (TypeConstructor, KindRep))] -> KindEnv -> Either ErrMsg KindEnv
makeKindEnv = go where
    getRank :: KindExpr -> Int
    getRank Star = 0
    getRank (kin1 `KArr` kin2) = max (getRank kin1 + 1) (getRank kin2)
    unRep :: KindRep -> Either ErrMsg KindExpr
    unRep krep = do
        (kin, loc) <- case krep of
            RStar loc -> return (Star, loc)
            RKArr loc krep1 krep2 -> do
                kin1 <- unRep krep1
                kin2 <- unRep krep2
                return (kin1 `KArr` kin2, loc)
            RKPrn loc krep -> do
                kin <- unRep krep
                return (kin, loc)
        if getRank kin > 1
            then Left ("desugaring-error[" ++ pprint 0 loc "]: the higher-order kind expression is not allowed.")
            else return kin
    go :: [(SLoc, (TypeConstructor, KindRep))] -> KindEnv -> Either ErrMsg KindEnv
    go [] kind_env = return kind_env
    go ((loc, (tcon, krep)) : triples) kind_env = case Map.lookup tcon kind_env of
        Just _ -> Left ("desugaring-error[" ++ pprint 0 loc "]: it is wrong to redeclare an already declared type construtor.")
        Nothing -> do
            kin <- unRep krep
            go triples (Map.insert tcon kin kind_env)

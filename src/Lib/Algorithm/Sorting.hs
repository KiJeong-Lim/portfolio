module Lib.Algorithm.Sorting where

import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import Data.Functor.Identity
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

getTSortedSCCs :: Ord node => Map.Map node (Set.Set node) -> [(Bool, Set.Set node)]
getTSortedSCCs = runIdentity . go where
    whenMaybe :: Applicative m => Bool -> m a -> m (Maybe a)
    whenMaybe cond ma = if cond then fmap Just ma else pure Nothing
    sortByRel :: Ord node => [node] -> StateT (Set.Set node) (ReaderT (node -> [node]) Identity) [node]
    sortByRel [] = return []
    sortByRel (cur : nexts) = do
        visteds <- get
        maybe_ges <- whenMaybe (not (cur `Set.member` visteds)) $ do
            put (Set.insert cur visteds)
            rel <- lift ask
            gts <- sortByRel (rel cur)
            return (cur : gts)
        lts <- sortByRel nexts
        return (maybe lts (\ges -> lts ++ ges) maybe_ges)
    splitByRel :: Ord node => [node] -> StateT (Set.Set node) (ReaderT (node -> [node]) Identity) [(Bool, Set.Set node)]
    splitByRel [] = return []
    splitByRel (cur : nexts) = do
        visteds <- get
        maybe_ges <- whenMaybe (not (cur `Set.member` visteds)) (sortByRel [cur])
        sets <- splitByRel nexts
        return (maybe sets (\ges -> (cur `elem` ges, Set.fromList ges) : sets) maybe_ges)
    go :: Ord node => Map.Map node (Set.Set node) -> Identity [(Bool, Set.Set node)]
    go getDigraph = do
        let getVertices = Set.toAscList (Map.keysSet getDigraph)
            getOuts node = Set.toAscList (maybe (error "Lib.Base.getTSortedSCCs.go.getOuts") id (Map.lookup node getDigraph))
            getIns node = [ node' | (node', nodes) <- Map.toAscList getDigraph, node `Set.member` nodes ]
        (sortedVertices, _) <- runReaderT (runStateT (sortByRel getVertices) Set.empty) getOuts
        (sortedSCCs, _) <- runReaderT (runStateT (splitByRel getVertices) Set.empty) getIns
        return sortedSCCs

sortByMerging :: (a -> a -> Bool) -> [a] -> [a]
sortByMerging = go where
    go :: (a -> a -> Bool) -> [a] -> [a]
    go leq [] = []
    go leq [x] = [x]
    go leq xs = case (take (length xs `div` 2) xs, drop (length xs `div` 2) xs) of
        (left, right) -> merge leq (go leq left) (go leq right)
    merge :: (a -> a -> Bool) -> [a] -> [a] -> [a]
    merge leq [] [] = []
    merge leq [] ys = ys
    merge leq xs [] = xs
    merge leq (x : xs) (y : ys)
        | x `leq` y = x : merge leq xs (y : ys)
        | otherwise = y : merge leq (x : xs) ys

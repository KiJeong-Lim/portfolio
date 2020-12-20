module Lib.Algorithm.Sorting where

import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import Data.Functor.Identity
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

getTSortedSCCs :: Ord node => Map.Map node (Set.Set node) -> [Set.Set node]
getTSortedSCCs = runIdentity . go where
    when :: Monad m => Bool -> m a -> m (Maybe a)
    when cond ma
        | cond = fmap Just ma
        | otherwise = return Nothing
    sortByRel :: Ord node => [node] -> StateT (Set.Set node) (ReaderT (node -> [node]) Identity) [node]
    sortByRel [] = return []
    sortByRel (cur : nexts) = do
        visteds <- get
        maybe_ges <- when (not (cur `Set.member` visteds)) $ do
            put (Set.insert cur visteds)
            rel <- lift ask
            gts <- sortByRel (rel cur)
            return (cur : gts)
        lts <- sortByRel nexts
        return (maybe lts (\ges -> lts ++ ges) maybe_ges)
    splitByRel :: Ord node => [node] -> StateT (Set.Set node) (ReaderT (node -> [node]) Identity) [Set.Set node]
    splitByRel [] = return []
    splitByRel (cur : nexts) = do
        visteds <- get
        maybe_ges <- when (not (cur `Set.member` visteds)) (sortByRel [cur])
        sets <- splitByRel nexts
        return (maybe sets (\ges -> Set.fromList ges : sets) maybe_ges)
    go :: Ord node => Map.Map node (Set.Set node) -> Identity [Set.Set node]
    go getDigraph = do
        let getVertices = Set.toAscList (Map.keysSet getDigraph)
            getOuts node = Set.toAscList (maybe (error "Src.Helper.ETC.getTSortedSCCs.go.getOuts") id (Map.lookup node getDigraph))
            getIns node = [ node' | (node', nodes) <- Map.toAscList getDigraph, node `Set.member` nodes ]
        (sortedVertices, _) <- runReaderT (runStateT (sortByRel getVertices) Set.empty) getOuts
        (sortedSCCs, _) <- runReaderT (runStateT (splitByRel getVertices) Set.empty) getIns
        return sortedSCCs

sortByMerging :: (a -> a -> Bool) -> [a] -> [a]
sortByMerging = go where
    go :: (a -> a -> Bool) -> [a] -> [a]
    go lt [] = []
    go lt [x] = [x]
    go lt xs = case (take (length xs `div` 2) xs, drop (length xs `div` 2) xs) of
        (left, right) -> merge lt (go lt left) (go lt right)
    merge :: (a -> a -> Bool) -> [a] -> [a] -> [a]
    merge lt [] [] = []
    merge lt [] ys = ys
    merge lt xs [] = xs
    merge lt (x : xs) (y : ys)
        | x `lt` y = x : merge lt (y : xs) ys
        | otherwise = y : merge lt xs (x : ys)

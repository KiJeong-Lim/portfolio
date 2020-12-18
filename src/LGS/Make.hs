module LGS.Make where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LGS.Util

theCsUniv :: Set.Set Char
theCsUniv = Set.fromList (['a' .. 'z'] ++ ['A' .. 'Z'] ++ " `~0123456789!@#$%^&*()-=_+[]\\{}|;\':\"\n,./<>?")

getCharSet :: CharSet -> Set.Set Char
getCharSet = go where
    go :: CharSet -> Set.Set Char
    go (CsSingle ch) = Set.singleton ch
    go (CsEnum ch1 ch2) = Set.fromAscList [ch1 .. ch2]
    go (chs1 `CsUnion` chs2) = go chs1 `Set.union` go chs2
    go (chs1 `CsDiff` chs2) = go chs1 `Set.difference` go chs2
    go CsUniv = theCsUniv

makeDFAfromREs :: [(RegEx, Maybe RegEx)] -> DFA
makeDFAfromREs = deleteDeadStates . makeMinimalDFA . makeDFAfromNFA . getUnitedNFAfromREs where
    mkstrict :: (a, b) -> (a, b)
    mkstrict pair = snd pair `seq` pair
    getUnitedNFAfromREs :: [(RegEx, Maybe RegEx)] -> NFA
    getUnitedNFAfromREs regexes = runIdentity go where
        getNewQ :: StateT (ParserS, Map.Map (ParserS, Maybe Char) (Set.Set ParserS)) Identity ParserS
        getNewQ = do
            (maximumOfQs, deltas) <- get
            put (maximumOfQs + 1, deltas)
            return maximumOfQs
        drawTransition :: ((ParserS, Maybe Char), ParserS) -> StateT (ParserS, Map.Map (ParserS, Maybe Char) (Set.Set ParserS)) Identity ()
        drawTransition (key, q) = do
            (maximumOfQs, deltas) <- get
            case Map.lookup key deltas of
                Nothing -> put (maximumOfQs, Map.insert key (Set.singleton q) deltas)
                Just qs -> put (maximumOfQs, Map.update (const (Just (Set.insert q qs))) key deltas)
        loop :: RegEx -> StateT (ParserS, Map.Map (ParserS, Maybe Char) (Set.Set ParserS)) Identity (ParserS, ParserS)
        loop (ReUnion regex1 regex2) = do
            (qi1, qf1) <- loop regex1
            (qi2, qf2) <- loop regex2
            qi <- getNewQ
            qf <- getNewQ
            drawTransition ((qi, Nothing), qi1)
            drawTransition ((qi, Nothing), qi2)
            drawTransition ((qf1, Nothing), qf)
            drawTransition ((qf2, Nothing), qf)
            return (qi, qf)
        loop (ReConcat regex1 regex2) = do
            (qi1, qf1) <- loop regex1
            (qi2, qf2) <- loop regex2
            drawTransition ((qf1, Nothing), qi2)
            return (qi1, qf2)
        loop (ReStar regex1) = do
            (qi1, qf1) <- loop regex1
            qi <- getNewQ
            qf <- getNewQ
            drawTransition ((qi, Nothing), qi1)
            drawTransition ((qf1, Nothing), qi1)
            drawTransition ((qf1, Nothing), qf)
            drawTransition ((qi, Nothing), qf)
            return (qi, qf)
        loop ReZero = do
            qi <- getNewQ
            qf <- getNewQ
            return (qi, qf)
        loop (ReWord str) = do
            let n = length str
            qs <- mapM (\_ -> getNewQ) [0, 1 .. n]
            mapM drawTransition (zip (zip (take n qs) (map Just str)) (drop 1 qs))
            return (qs !! 0, qs !! n)
        loop (ReCharSet chs) = do
            qi <- getNewQ
            qf <- getNewQ
            mapM drawTransition (zip (zip (repeat qi) (map Just (Set.toList (getCharSet chs)))) (repeat qf))
            return (qi, qf)
        loop (ReDagger regex1) = do
            (qi1, qf1) <- loop regex1
            qi <- getNewQ
            qf <- getNewQ
            drawTransition ((qi, Nothing), qi1)
            drawTransition ((qf1, Nothing), qi1)
            drawTransition ((qf1, Nothing), qf)
            return (qi, qf)
        loop (ReQuest regex1) = do
            (qi1, qf1) <- loop regex1
            qi <- getNewQ
            qf <- getNewQ
            drawTransition ((qi, Nothing), qi1)
            drawTransition ((qf1, Nothing), qf)
            drawTransition ((qi, Nothing), qf)
            return (qi, qf)
        go :: Identity NFA
        go = do
            let n = length regexes
            (markeds, (numberOfQs, deltas)) <- flip runStateT (n + 1, Map.empty) $ fmap (Map.fromAscList . concat) $ sequence
                [ case regexes !! (i - 1) of
                    (regex, Nothing) -> do
                        (qi, qf) <- loop regex
                        drawTransition ((0, Nothing), qi)
                        drawTransition ((qf, Nothing), i)
                        return []
                    (regex1, Just regex2) -> do
                        (qi1, qf1) <- loop regex1
                        (qi2, qf2) <- loop regex2
                        q <- getNewQ
                        drawTransition ((0, Nothing), qi1)
                        drawTransition ((qf1, Nothing), q)
                        drawTransition ((q, Nothing), qi2)
                        drawTransition ((qf2, Nothing), i)
                        return [(i, q)]
                | i <- [1, 2 .. n]
                ]
            return $ NFA 
                { getInitialQOfNFA = 0
                , getFinalQsOfNFA = Set.fromAscList [1, 2 .. n]
                , getTransitionsOfNFA = deltas
                , getMarkedQsOfNFA = markeds
                }
    makeDFAfromNFA :: NFA -> DFA
    makeDFAfromNFA (NFA q0 qfs deltas markeds) = runIdentity go where
        eClosure :: Set.Set ParserS -> Set.Set ParserS
        eClosure qs = if qs == qs' then qs' else eClosure qs' where
            qs' :: Set.Set ParserS
            qs' = foldr Set.union qs
                [ case Map.lookup (q, Nothing) deltas of
                    Nothing -> Set.empty
                    Just ps -> ps
                | q <- Set.toList qs
                ]
        getNexts :: Set.Set ParserS -> Char -> Set.Set ParserS
        getNexts qs ch = Set.unions
            [ case Map.lookup (q, Just ch) deltas of
                Nothing -> Set.empty
                Just ps -> ps
            | q <- Set.toList qs
            ]
        drawGraph :: Map.Map (Set.Set ParserS) ParserS -> [((Set.Set ParserS, ParserS), Char)] -> StateT (Map.Map (ParserS, Char) ParserS) Identity (Map.Map (Set.Set ParserS) ParserS)
        drawGraph mapOldToNew [] = return mapOldToNew
        drawGraph mapOldToNew (((qs, q'), ch) : triples) = do
            let ps = eClosure (getNexts qs ch)
            deltas' <- get
            case Map.lookup ps mapOldToNew of
                Nothing -> do
                    let p' = Map.size mapOldToNew
                    put (Map.insert (q', ch) p' deltas')
                    drawGraph (Map.insert ps p' mapOldToNew) triples
                Just p' -> do
                    put (Map.insert (q', ch) p' deltas')
                    drawGraph mapOldToNew triples
        loop :: Map.Map (Set.Set ParserS) ParserS -> StateT (Map.Map (ParserS, Char) ParserS) Identity (Map.Map ParserS ParserS, Map.Map ParserS (Set.Set ParserS))
        loop mapOldToNew = do
            mapOldToNew' <- drawGraph mapOldToNew ((,) <$> Map.toList mapOldToNew <*> Set.toList theCsUniv)
            if mapOldToNew == mapOldToNew'
                then return
                    ( Map.fromList
                        [ (q', qf)
                        | qf <- Set.toDescList qfs
                        , (qs, q') <- Map.toList mapOldToNew'
                        , qf `Set.member` qs
                        ]
                    , Map.fromAscList
                        [ mkstrict
                            ( i
                            , Set.fromList
                                [ q' 
                                | (qs, q') <- Map.toList mapOldToNew'
                                , q `Set.member` qs
                                ]
                            )
                        | (i, q) <- Map.toAscList markeds
                        ]
                    )
                else loop mapOldToNew'
        go :: Identity DFA
        go = do
            let q0' = 0
            ((qfs', markeds'), deltas') <- runStateT (loop (Map.singleton (eClosure (Set.singleton q0)) q0')) Map.empty
            return (DFA q0' qfs' deltas' markeds')
    makeMinimalDFA :: DFA -> DFA
    makeMinimalDFA (DFA q0 qfs deltas markeds) = minimal_dfa where
        reachables :: Set.Set ParserS
        reachables = go (Set.singleton q0) where
            go :: Set.Set ParserS -> Set.Set ParserS
            go qs = if qs == qs' then qs' else go qs' where
                qs' :: Set.Set ParserS
                qs' = foldr Set.insert qs
                    [ p
                    | ((q, _), p) <- Map.toList deltas
                    , q `Set.member` qs
                    ]
        distinguishedPairs :: Set.Set (ParserS, ParserS)
        distinguishedPairs = go initialPairs where
            initialPairs :: Set.Set (ParserS, ParserS)
            initialPairs = Set.fromAscList
                [ (q, q')
                | q <- Set.toAscList reachables
                , q' <- Set.toAscList reachables
                , Map.lookup q qfs /= Map.lookup q' qfs
                ]
            go :: Set.Set (ParserS, ParserS) -> Set.Set (ParserS, ParserS)
            go pairs = if pairs == pairs' then pairs' else go pairs' where
                pairs' :: Set.Set (ParserS, ParserS)
                pairs' = foldr Set.union pairs
                    [ Set.fromAscList
                        [ (q, q')
                        | q <- Set.toAscList reachables
                        , q' <- Set.toAscList reachables
                        , (deltas Map.! (q, ch), deltas Map.! (q', ch)) `Set.member` pairs
                        ]
                    | ch <- Set.toList theCsUniv
                    ]
        winners :: Set.Set ParserS
        winners = go q0 (Set.toList reachables) where
            go :: ParserS -> [ParserS] -> Set.Set ParserS
            go p qs = case [ q | q <- qs, (p, q) `Set.member` distinguishedPairs ] of
                [] -> Set.singleton p
                p' : qs' -> Set.insert p (go p' qs')
        minimal_dfa :: DFA
        minimal_dfa = DFA
            { getInitialQOfDFA = q0
            , getFinalQsOfDFA = Map.fromAscList
                [ (qf, label)
                | (qf, label) <- Map.toAscList qfs
                , qf `Set.member` winners
                ]
            , getTransitionsOfDFA = Map.fromAscList
                [ mkstrict
                    ( (q, ch)
                    , head
                        [ q'
                        | q' <- Set.toList winners
                        , not ((q', p) `Set.member` distinguishedPairs)
                        ]
                    )
                | ((q, ch), p) <- Map.toAscList deltas
                , q `Set.member` winners
                ]
            , getMarkedQsOfDFA = Map.map (Set.filter (\q -> q `Set.member` winners)) markeds
            }
    deleteDeadStates :: DFA -> DFA
    deleteDeadStates (DFA q0 qfs deltas markeds) = runIdentity go where
        edges :: Set.Set (ParserS, ParserS)
        edges = Set.fromList [ (p, q) | ((q, ch), p) <- Map.toList deltas ]
        loop :: [ParserS] -> StateT (Set.Set ParserS) Identity ()
        loop ps = do
            forM ps $ \p -> do
                visiteds <- get
                when (not (p `Set.member` visiteds)) $ do
                    modify (Set.insert p)
                    loop [ q' | (p', q') <- Set.toList edges, p == p' ]
            return ()
        go :: Identity DFA
        go = do
            (_, winners) <- runStateT (loop (Set.toList (Map.keysSet qfs))) Set.empty
            return $ DFA
                { getInitialQOfDFA = q0
                , getFinalQsOfDFA = qfs
                , getTransitionsOfDFA = Map.fromAscList
                    [ ((q, ch), p)
                    | ((q, ch), p) <- Map.toAscList deltas
                    , q `Set.member` winners
                    , p `Set.member` winners
                    ]
                , getMarkedQsOfDFA = Map.map (Set.filter (\q -> q `Set.member` winners)) markeds
                }

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
import Lib.Base

theCsUniv :: Set.Set Char
theCsUniv = Set.fromList (['a' .. 'z'] ++ ['A' .. 'Z'] ++ " `~0123456789!@#$%^&*()-=_+[]\\{}|;\':\"\n,./<>?")

runCharSet :: CharSet -> Set.Set Char
runCharSet = go where
    go :: CharSet -> Set.Set Char
    go (CsSingle ch) = Set.singleton ch
    go (CsEnum ch1 ch2) = Set.fromAscList [ch1 .. ch2]
    go (chs1 `CsUnion` chs2) = go chs1 `Set.union` go chs2
    go (chs1 `CsDiff` chs2) = go chs1 `Set.difference` go chs2
    go CsUniv = theCsUniv

mkstrict :: (a, b) -> (a, b)
mkstrict pair = fst pair `seq` snd pair `seq` pair

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
        mapM drawTransition (zip (zip (repeat qi) (map Just (Set.toList (runCharSet chs)))) (repeat qf))
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
makeDFAfromNFA (NFA q0 qfs deltas markeds) = runIdentity result where
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
    go :: Map.Map (Set.Set ParserS) ParserS -> StateT (Map.Map (ParserS, Char) ParserS) Identity (Map.Map ParserS ParserS, Map.Map ParserS (Set.Set ParserS))
    go mapOldToNew = do
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
            else go mapOldToNew'
    result :: Identity DFA
    result = do
        let q0' = 0
        ((qfs', markeds'), deltas') <- runStateT (go (Map.singleton (eClosure (Set.singleton q0)) q0')) Map.empty
        qfs' `seq` markeds' `seq` deltas' `seq` return (DFA q0' qfs' deltas' markeds')

makeMinimalDFA :: DFA -> DFA
makeMinimalDFA (DFA q0 qfs deltas markeds) = result where
    theSetOfAllStates :: Set.Set ParserS
    theSetOfAllStates = Set.unions
        [ Set.singleton q0
        , Map.keysSet qfs
        , Set.map fst (Map.keysSet deltas)
        , Set.fromList (Map.elems deltas)
        ]
    theCharSet :: Set.Set Char
    theCharSet = Set.map snd (Map.keysSet deltas)
    initialKlasses :: [Set.Set ParserS]
    initialKlasses = (theSetOfAllStates `Set.difference` Map.keysSet qfs) : Map.elems (foldr loop1 Map.empty (Map.toList qfs)) where
        loop1 :: (ParserS, ParserS) -> Map.Map ParserS (Set.Set ParserS) -> Map.Map ParserS (Set.Set ParserS)
        loop1 (qf, label) = Map.alter (Just . maybe (Set.singleton qf) (Set.insert qf)) label
    finalKlasses :: [Set.Set ParserS]
    finalKlasses = splitKlasses initialKlasses initialKlasses where
        splitKlasses :: [Set.Set ParserS] -> [Set.Set ParserS] -> [Set.Set ParserS]
        splitKlasses result stack
            | null stack = result
            | otherwise = uncurry splitKlasses (Set.foldr (uncurry . loop1 (head stack)) (result, tail stack) theCharSet)
        loop1 :: Set.Set ParserS -> Char -> [Set.Set ParserS] -> [Set.Set ParserS] -> ([Set.Set ParserS], [Set.Set ParserS])
        loop1 top ch = foldr (>=>) return . map loop2 where
            focused :: Set.Set ParserS
            focused = Set.filter (\q -> maybe False (\p -> p `Set.member` top) (Map.lookup (q, ch) deltas)) theSetOfAllStates
            loop2 :: Set.Set ParserS -> [Set.Set ParserS] -> ([Set.Set ParserS], [Set.Set ParserS])
            loop2 klass stack
                | Set.null intersection = ([klass], stack)
                | Set.null difference = ([klass], stack)
                | otherwise = mkstrict
                    ( [intersection, difference]
                    , case klass `List.elemIndex` stack of
                        Nothing -> if Set.size intersection <= Set.size difference then intersection : stack else difference : stack
                        Just idx -> [intersection, difference] ++ take idx stack ++ drop (idx + 1) stack
                    )
                where
                    intersection :: Set.Set ParserS
                    intersection = klass `Set.intersection` focused
                    difference :: Set.Set ParserS
                    difference = klass `Set.difference` focused
    convert :: ParserS -> ParserS
    convert q = head
        [ q'
        | (q', qs) <- zip [0, 1 .. ] finalKlasses
        , q `Set.member` qs
        ]
    result :: DFA
    result = DFA
        { getInitialQOfDFA = convert q0
        , getFinalQsOfDFA = Map.fromList
            [ (convert qf, label) 
            | (qf, label) <- Map.toList qfs
            ]
        , getTransitionsOfDFA = Map.fromList
            [ ((convert q, ch), convert p)
            | ((q, ch), p) <- Map.toList deltas
            ]
        , getMarkedQsOfDFA = Map.map (Set.map convert) markeds
        }

deleteDeadStates :: DFA -> DFA
deleteDeadStates (DFA q0 qfs deltas markeds) = result where
    edges :: Map.Map ParserS (Set.Set ParserS)
    edges = foldr go Map.empty [ (p, q) | ((q, ch), p) <- Map.toList deltas ] where
        go :: (ParserS, ParserS) -> Map.Map ParserS (Set.Set ParserS) -> Map.Map ParserS (Set.Set ParserS)
        go (p, q) = Map.alter (Just . maybe (Set.singleton q) (Set.insert q)) p
    winners :: Set.Set ParserS
    winners = go (Set.toAscList (Map.keysSet qfs)) Set.empty where
        go :: [ParserS] -> Set.Set ParserS -> Set.Set ParserS
        go [] ps = ps
        go (q : qs) ps = if q `Set.member` ps then go qs ps else go (maybe [] Set.toAscList (Map.lookup q edges) ++ qs) (Set.insert q ps)
    result :: DFA
    result = DFA
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

makeDFAfromREs :: [(RegEx, Maybe RegEx)] -> DFA
makeDFAfromREs = deleteDeadStates . makeMinimalDFA . makeDFAfromNFA . getUnitedNFAfromREs

mkCsSingle :: Char -> CharSet
mkCsSingle ch1 = ch1 `seq` CsSingle ch1

mkCsEnum :: Char -> Char -> CharSet
mkCsEnum ch1 ch2 = ch1 `seq` ch2 `seq` CsEnum ch1 ch2

mkCsUnion :: CharSet -> CharSet -> CharSet
mkCsUnion chs1 chs2 = chs1 `seq` chs2 `seq` CsUnion chs1 chs2

mkCsDiff :: CharSet -> CharSet -> CharSet
mkCsDiff chs1 chs2 = chs1 `seq` chs2 `seq` CsDiff chs1 chs2

mkCsUniv :: CharSet
mkCsUniv = CsUniv

mkReZero :: RegEx
mkReZero = ReZero

mkReUnion :: RegEx -> RegEx -> RegEx
mkReUnion (ReZero) re1 = re1
mkReUnion re1 (ReZero) = re1
mkReUnion re1 re2 = ReUnion re1 re2

mkReWord :: String -> RegEx
mkReWord str = str `seq` ReWord str

mkReConcat :: RegEx -> RegEx -> RegEx
mkReConcat (ReZero) re1 = ReZero
mkReConcat re1 (ReZero) = ReZero
mkReConcat (ReWord str1) (ReWord str2) = mkReWord (str1 ++ str2)
mkReConcat (ReWord []) re1 = re1
mkReConcat re1 (ReWord []) = re1
mkReConcat re1 re2 = ReConcat re1 re2

mkReStar :: RegEx -> RegEx
mkReStar (ReZero) = mkReWord []
mkReStar (ReWord []) = mkReWord []
mkReStar (ReStar re1) = mkReStar re1
mkReStar (ReDagger re1) = mkReStar re1
mkReStar (ReQuest re1) = mkReStar re1
mkReStar re1 = ReStar re1

mkReDagger :: RegEx -> RegEx
mkReDagger (ReZero) = mkReWord []
mkReDagger (ReWord []) = mkReWord []
mkReDagger (ReStar re1) = mkReStar re1
mkReDagger (ReDagger re1) = mkReDagger re1
mkReDagger (ReQuest re1) = mkReStar re1
mkReDagger re1 = ReDagger re1

mkReQuest :: RegEx -> RegEx
mkReQuest (ReZero) = mkReWord []
mkReQuest (ReWord []) = mkReWord []
mkReQuest (ReStar re1) = mkReStar re1
mkReQuest (ReDagger re1) = mkReStar re1
mkReQuest (ReQuest re1) = mkReQuest re1
mkReQuest re1 = ReQuest re1

mkReCharSet :: CharSet -> RegEx
mkReCharSet chs = chs `seq` ReCharSet chs

differentiate :: RegEx -> Char -> RegEx
differentiate (ReZero) ch = mkReZero
differentiate (ReUnion re1 re2) ch = mkReUnion (differentiate re1 ch) (differentiate re2 ch)
differentiate (ReWord str1) ch = if null str1 then mkReZero else if head str1 == ch then mkReWord (tail str1) else mkReZero
differentiate (ReConcat re1 re2) ch = mkReUnion (mkReConcat (differentiate re1 ch) re2) (if isNullable re1 then differentiate re2 ch else mkReZero)
differentiate (ReStar re1) ch = mkReConcat (differentiate re1 ch) (mkReStar re1)
differentiate (ReDagger re1) ch = differentiate (mkReConcat re1 (mkReStar re1)) ch
differentiate (ReQuest re1) ch = differentiate (mkReUnion re1 (mkReWord [])) ch
differentiate (ReCharSet chs1) ch = if ch `Set.member` runCharSet chs1 then mkReWord [] else mkReZero

runRegEx :: RegEx -> String -> Bool
runRegEx = curry (isNullable . uncurry (List.foldl' differentiate))

isNullable :: RegEx -> Bool
isNullable (ReZero) = False
isNullable (ReUnion re1 re2) = isNullable re1 || isNullable re2
isNullable (ReWord str1) = null str1
isNullable (ReConcat re1 re2) = isNullable re1 && isNullable re2
isNullable (ReStar re1) = True
isNullable (ReDagger re1) = isNullable re1
isNullable (ReQuest re1) = True
isNullable (ReCharSet chs1) = False

implies :: RegEx -> RegEx -> Bool
implies = go where
    go :: RegEx -> RegEx -> Bool
    go re1 re2 = re1 == re2 || dispatch re1 re2
    dispatch :: RegEx -> RegEx -> Bool
    dispatch (ReZero) re1 = True
    dispatch (ReUnion re1 re2) re3 = re1 `implies` re3 && re2 `implies` re3
    dispatch (ReWord str1) re2 = runRegEx re2 str1
    dispatch (ReCharSet chs1) (ReCharSet chs2) = runCharSet chs1 `Set.isSubsetOf` runCharSet chs2
    dispatch (ReCharSet chs1) (ReWord [ch2]) = runCharSet chs1 `Set.isSubsetOf` Set.singleton ch2
    dispatch (ReStar re1) (ReStar re2) = re1 `implies` re2
    dispatch (ReStar re1) (ReDagger re2) = isNullable re2 && re1 `implies` ReStar re2
    dispatch (ReStar re1) (ReQuest re2) = ReStar re1 `implies` re2
    dispatch (ReDagger re1) (ReStar re2) = re1 `implies` re2
    dispatch (ReDagger re1) (ReDagger re2) = re1 `implies` re2
    dispatch (ReDagger re1) (ReQuest re2) = ReStar re1 `implies` re2
    dispatch (ReQuest re1) (ReStar re2) = re1 `implies` ReStar re2
    dispatch (ReQuest re1) (ReDagger re2) = isNullable re2 && re1 `implies` ReStar re2
    dispatch (ReQuest re1) (ReQuest re2) = re1 `implies` re2
    dispatch (ReConcat re1 re2) (ReStar re3) = re1 `implies` ReStar re3 && re2 `implies` ReStar re3
    dispatch (ReConcat re1 re2) (ReDagger re3) = (re1 `implies` ReDagger re3 && re2 `implies` ReStar re3) || (re1 `implies` ReStar re3 && re2 `implies` ReDagger re3)
    dispatch re1 (ReUnion re2 re3) = re1 `implies` re2 || re1 `implies` re3
    dispatch re1 (ReStar re2) = re1 `implies` ReWord [] || re1 `implies` re2
    dispatch re1 (ReDagger re2) = re1 `implies` re2
    dispatch re1 (ReQuest re2) = re1 `implies` ReWord [] || re1 `implies` re2
    dispatch re1 re2 = False

equiv :: RegEx -> RegEx -> Bool
re1 `equiv` re2 = re1 `implies` re2 && re2 `implies` re1

reduceRegEx :: RegEx -> RegEx
reduceRegEx = go3 . go2 . go1 where
    dropLast :: [x] -> [x]
    dropLast [] = []
    dropLast [x1] = []
    dropLast (x1 : xs) = x1 : dropLast xs
    unfoldConcat :: RegEx -> [RegEx]
    unfoldConcat (ReConcat re1 re2) = unfoldConcat re1 ++ unfoldConcat re2
    unfoldConcat (ReWord []) = []
    unfoldConcat re1 = [re1]
    extractCS :: [Char] -> RegEx
    extractCS chs
        = case reverse (foldr loop1 [] chs) of
            [] -> mkReZero
            pair : pairs -> case foldr mkCsUnion (loop2 pair) (map loop2 pairs) of
                CsSingle ch -> mkReWord [ch]
                chs' -> mkReCharSet chs'
        where
            loop1 :: Char -> [(Char, Char)] -> [(Char, Char)]
            loop1 ch0 pairs0 = case List.partition (\pair -> snd pair == pred ch0) pairs0 of
                ([], pairs1) -> (ch0, ch0) : pairs1
                ([(ch1, ch2)], pairs1) -> (ch1, ch0) : pairs1
            loop2 :: (Char, Char) -> CharSet
            loop2 (ch1, ch2) = if ch1 == ch2 then mkCsSingle ch1 else mkCsEnum ch1 ch2
    go1 :: RegEx -> RegEx
    go1 (ReZero) = makeReZero1
    go1 (ReUnion re1 re2) = makeReUnion1 (go1 re1) (go1 re2)
    go1 (ReWord str1) = makeReWord1 str1
    go1 (ReConcat re1 re2) = makeReConcat1 (go1 re1) (go1 re2)
    go1 (ReStar re1) = makeReStar1 (go1 re1)
    go1 (ReDagger re1) = makeReDagger1 (go1 re1)
    go1 (ReQuest re1) = makeReQuest1 (go1 re1)
    go1 (ReCharSet chs1) = makeReCharSet1 chs1
    makeReZero1 :: RegEx
    makeReZero1 = mkReZero
    makeReUnion1 :: RegEx -> RegEx -> RegEx
    makeReUnion1 re1 re2
        | ReCharSet chs1 <- re1
        , ReCharSet chs2 <- re2
        = makeReCharSet1 (mkCsUnion chs1 chs2)
        | re1 `implies` re2
        = re2
        | re2 `implies` re1
        = re1
        | ReUnion re3 re4 <- re2
        = mkReUnion (mkReUnion re1 re3) re4
        | otherwise
        = mkReUnion re1 re2
    makeReWord1 :: String -> RegEx
    makeReWord1 str1
        = case str1 of
            [ch1] -> mkReCharSet (mkCsSingle ch1)
            str1' -> mkReWord str1'
    makeReConcat1 :: RegEx -> RegEx -> RegEx
    makeReConcat1 re1 re2
        | ReConcat re3 re4 <- re2
        = mkReConcat (mkReConcat re1 re3) re4
        | otherwise
        = mkReConcat re1 re2
    makeReStar1 :: RegEx -> RegEx
    makeReStar1 re1
        = case deleteUnit re1 of
            ReZero -> mkReWord []
            re2 -> case destructStarConcat re2 of
                [] -> mkReStar re2
                re3 : res4 -> mkReStar (List.foldl' mkReUnion re3 res4)
        where
            deleteUnit :: RegEx -> RegEx
            deleteUnit (ReUnion re1 (ReWord [])) = deleteUnit re1
            deleteUnit (ReUnion re1 re2) = mkReUnion (deleteUnit re1) re2
            deleteUnit (ReWord []) = ReZero
            deleteUnit re1 = re1
            destructStarConcat :: RegEx -> [RegEx]
            destructStarConcat (ReStar re1)
                = [re1]
            destructStarConcat (ReConcat re1 (ReStar re2))
                = case destructStarConcat re1 of
                    [] -> []
                    res3 -> res3 ++ [re2]
            destructStarConcat re1
                = []
    makeReDagger1 :: RegEx -> RegEx
    makeReDagger1 = makeReConcat1 <*> makeReStar1
    makeReQuest1 :: RegEx -> RegEx
    makeReQuest1 re1 = makeReUnion1 (makeReWord1 []) re1
    makeReCharSet1 :: CharSet -> RegEx
    makeReCharSet1 (CsUnion chs1 chs2)
        = case (runCharSet chs1, runCharSet chs2) of
            (chs1_val, chs2_val)
                | chs1_val `Set.isSubsetOf` chs2_val -> mkReCharSet chs2
                | chs2_val `Set.isSubsetOf` chs1_val -> mkReCharSet chs1
                | otherwise -> case List.partition (\ch -> ch `Set.member` chs1_val || ch `Set.member` chs2_val) (Set.toDescList theCsUniv) of
                    (yess, nos)
                        | length nos < 5 -> mkReCharSet (List.foldl' mkCsDiff mkCsUniv (map mkCsSingle nos))
                        | otherwise -> extractCS yess
    makeReCharSet1 chs1
        = extractCS (Set.toAscList (runCharSet chs1))
    go2 :: RegEx -> RegEx
    go2 (ReZero) = makeReZero2
    go2 (ReUnion re1 re2) = makeReUnion2 (go2 re1) (go2 re2)
    go2 (ReWord str1) = makeReWord2 str1
    go2 (ReConcat re1 re2) = makeReConcat2 (go2 re1) (go2 re2)
    go2 (ReStar re1) = makeReStar2 (go2 re1)
    go2 (ReDagger re1) = makeReDagger2 (go2 re1)
    go2 (ReCharSet chs1) = makeReCharSet2 chs1
    makeReZero2 :: RegEx
    makeReZero2 = mkReZero
    makeReUnion2 :: RegEx -> RegEx -> RegEx
    makeReUnion2 re1 re2
        | ReDagger re3 <- re1
        , ReWord [] <- re2
        = mkReStar re3
        | ReWord [] <- re1
        , ReDagger re3 <- re2
        = mkReStar re3
        | ReStar re3 <- re1
        , ReWord [] <- re2
        = re1
        | ReWord [] <- re1
        , ReStar re3 <- re2
        = re2
        | ReQuest re3 <- re1
        , ReWord [] <- re2
        = re1
        | ReWord [] <- re1
        , ReQuest re3 <- re2
        = re2
        | ReWord [] <- re1
        = mkReQuest re2
        | ReWord [] <- re2
        = mkReQuest re1
        | otherwise
        = makeReUnion1 re1 re2
    makeReWord2 :: String -> RegEx
    makeReWord2 = mkReWord
    makeReConcat2 :: RegEx -> RegEx -> RegEx
    makeReConcat2 re1 re2
        | ReWord str1 <- re1
        , ReWord str2 <- re2
        = mkReWord (str1 ++ str2)
        | ReStar re3 <- re1
        , ReStar re4 <- re2
        , re3 `equiv` re4
        = re1
        | ReStar re3 <- re1
        , ReDagger re4 <- re2
        , re3 `equiv` re4
        = re2
        | ReStar re3 <- re1
        , ReQuest re4 <- re2
        , re3 `equiv` re4
        = re1
        | ReDagger re3 <- re1
        , ReStar re4 <- re2
        , re3 `equiv` re4
        = re1
        | ReDagger re3 <- re1
        , ReQuest re4 <- re2
        , re3 `equiv` re4
        = re1
        | ReQuest re3 <- re1
        , ReStar re4 <- re2
        , re3 `equiv` re4
        = re2
        | ReQuest re3 <- re1
        , ReDagger re4 <- re2
        , re3 `equiv` re4
        = re2
        | ReStar re3 <- re1
        , re2 `equiv` re3
        = mkReDagger re3
        | ReStar re3 <- re2
        , re1 `equiv` re3
        = mkReDagger re3
        | ReConcat re3 re4 <- re1
        = case makeReConcat2 re4 re2 of
            ReConcat re5 re6 -> makeReConcat1 (makeReConcat2 re3 re5) re6
            re5 -> makeReConcat2 re3 re5
        | otherwise
        = makeReConcat1 re1 re2
    makeReStar2 :: RegEx -> RegEx
    makeReStar2 = mkReStar
    makeReDagger2 :: RegEx -> RegEx
    makeReDagger2 = mkReDagger
    makeReQuest2 :: RegEx -> RegEx
    makeReQuest2 = mkReQuest
    makeReCharSet2 :: CharSet -> RegEx
    makeReCharSet2 chs1
        = case List.partition (\ch -> ch `Set.member` runCharSet chs1) (Set.toDescList theCsUniv) of
            (yess, nos)
                | length nos < 5 -> mkReCharSet (List.foldl' mkCsDiff mkCsUniv (map mkCsSingle nos))
                | otherwise -> case reverse (mkCollection yess) of
                    [] -> mkReZero
                    re1 : res2 -> case List.foldl' mkCsUnion re1 res2 of
                        CsSingle ch3 -> ReWord [ch3]
                        chs3 -> mkReCharSet chs3
        where
            loop :: Char -> [(Char, Char)] -> [(Char, Char)]
            loop ch0 pairs0 = case List.partition (\pair -> snd pair == pred ch0) pairs0 of
                ([], pairs1) -> (ch0, ch0) : pairs1
                ([(ch1, ch2)], pairs1) -> (ch1, ch0) : pairs1
            mkCollection :: [Char] -> [CharSet]
            mkCollection yess = do
                (ch1, ch2) <- foldr loop [] yess
                if ch1 == ch2
                    then return (mkCsSingle ch1)
                    else return (mkCsEnum ch1 ch2)
    makeReZero3 :: RegEx
    makeReZero3 = mkReZero
    makeReUnion3 :: RegEx -> RegEx -> RegEx
    makeReUnion3 re1 re2
        | ReQuest re3 <- re1
        = mkReQuest (makeReUnion3 re3 re2)
        | ReQuest re3 <- re2
        = mkReQuest (makeReUnion3 re1 re3)
        | ReUnion re3 re4 <- re1
        = case makeReUnion3 re4 re2 of
            ReUnion re5 re6 -> makeReUnion2 (makeReUnion3 re3 re5) re6
            re5 -> makeReUnion3 re3 re5
        | otherwise
        = case go (unfoldConcat re1) (unfoldConcat re2) of
            Nothing -> makeReUnion2 re1 re2
            Just re3 -> re3
        where
            go :: [RegEx] -> [RegEx] -> Maybe RegEx
            go res1 res2
                | null res1 || null res2 = return (tryToMerge res1 res2)
                | Just res3 <- head res1 `matchPrefix` res2 = do
                    re4 <- go (tail res1) res3
                    return (mkReConcat (head res1) re4)
                | Just res3 <- last res1 `matchSuffix` res2 = do
                    re4 <- go (dropLast res1) res3
                    return (mkReConcat re4 (last res1))
                | otherwise = Nothing
            tryToMerge :: [RegEx] -> [RegEx] -> RegEx
            tryToMerge [] [] = makeReWord2 []
            tryToMerge [] (re1 : res2) = makeReQuest2 (List.foldl' makeReConcat2 re1 res2)
            tryToMerge (re1 : res2) [] = makeReQuest2 (List.foldl' makeReConcat2 re1 res2)
            tryToMerge (re1 : res2) (re3 : res4) = makeReUnion2 (List.foldl' makeReConcat2 re1 res2) (List.foldl' makeReConcat2 re3 res4)
    makeReWord3 :: String -> RegEx
    makeReWord3 = mkReWord
    makeReConcat3 :: RegEx -> RegEx -> RegEx
    makeReConcat3 = makeReConcat2
    makeReStar3 :: RegEx -> RegEx
    makeReStar3 re0
        | ReConcat re1 re2 <- re0
        = case foldr loop1 init1 (unfoldConcat re1 ++ unfoldConcat re2) of
            Nothing -> makeReStar2 (mkReConcat re1 re2)
            Just (re3', res4) -> case (re3', res4) of
                (Nothing, []) -> mkReWord []
                (Nothing, re5 : res6) -> mkReStar (List.foldl' makeReUnion3 re5 res6)
                (Just re5, res6) -> mkReStar (List.foldl' makeReUnion1 re5 res6)
        | otherwise
        = makeReStar2 re0
        where
            init1 :: Maybe (Maybe RegEx, [RegEx])
            init1 = Just (Nothing, [])
            loop1 :: RegEx -> Maybe (Maybe RegEx, [RegEx]) -> Maybe (Maybe RegEx, [RegEx])
            loop1 (ReStar re1) acc = do
                (re2', res3) <- acc
                return (re2', re1 : res3)
            loop1 re1 acc = do
                (re2', res3) <- acc
                case re2' of
                    Nothing -> return (Just re1, res3)
                    Just re2 -> Nothing
    makeReDagger3 :: RegEx -> RegEx
    makeReDagger3 = mkReDagger
    makeReQuest3 :: RegEx -> RegEx
    makeReQuest3 = mkReQuest
    makeReCharSet3 :: CharSet -> RegEx
    makeReCharSet3 = mkReCharSet
    go3 :: RegEx -> RegEx
    go3 (ReZero) = makeReZero3
    go3 (ReUnion re1 re2) = makeReUnion3 (go3 re1) (go3 re2)
    go3 (ReWord str1) = makeReWord3 str1
    go3 (ReConcat re1 re2) = makeReConcat3 (go3 re1) (go3 re2)
    go3 (ReStar re1) = makeReStar3 (go3 re1)
    go3 (ReDagger re1) = makeReDagger3 (go3 re1)
    go3 (ReQuest re1) = makeReQuest3 (go3 re1)
    go3 (ReCharSet chs1) = makeReCharSet3 chs1
    matchPrefix :: RegEx -> [RegEx] -> Maybe [RegEx]
    matchPrefix re1 res2 = if re1 `equiv` head res2 then return (tail res2) else Nothing
    matchSuffix :: RegEx -> [RegEx] -> Maybe [RegEx]
    matchSuffix re1 res2 = if re1 `equiv` last res2 then return (dropLast res2) else Nothing

makeJumpRegexTable :: DFA -> Map.Map (ParserS, ParserS) RegEx
makeJumpRegexTable (DFA q0 qfs delta markeds) = makeClosure (length qs) where
    qs :: [ParserS]
    qs = Set.toAscList theSetOfAllStatesInGraph where
        theSetOfAllStatesInGraph :: Set.Set ParserS
        theSetOfAllStatesInGraph = Set.unions
            [ Set.singleton q0
            , Map.keysSet qfs
            , Set.unions [ Set.fromList [q, p] | ((q, ch), p) <- Map.toAscList delta ]
            ]
    makeRegExFromCharSet :: (Char -> Bool) -> RegEx
    makeRegExFromCharSet cond
        = case List.partition cond (Set.toDescList theCsUniv) of
            (yess, nos)
                | length nos < 5 -> mkReCharSet (List.foldl' mkCsDiff mkCsUniv (map mkCsSingle nos))
                | otherwise -> foldr mkReUnion mkReZero
                    [ case pair of
                        (ch1, ch2) -> if ch1 == ch2 then mkReWord [ch1] else mkReCharSet (mkCsEnum ch1 ch2)
                    | pair <- foldr loop [] yess
                    ]
        where
            loop :: Char -> [(Char, Char)] -> [(Char, Char)]
            loop ch0 pairs0 = case List.partition (\pair -> snd pair == pred ch0) pairs0 of
                ([], pairs1) -> (ch0, ch0) : pairs1
                ([(ch1, ch2)], pairs1) -> (ch1, ch0) : pairs1
    lookTable :: Map.Map (ParserS, ParserS) RegEx -> (ParserS, ParserS) -> RegEx
    lookTable table = maybe ReZero id . flip Map.lookup table
    makeClosure :: Int -> Map.Map (ParserS, ParserS) RegEx
    makeClosure n
        | n < 0 = undefined
        | n == 0 = init
        | n > 0 = loop (qs !! (n - 1)) (makeClosure (n - 1))
        where
            init :: Map.Map (ParserS, ParserS) RegEx
            init = fromMaybeList
                [ case reduceRegEx (mkReUnion (if q1 == q2 then mkReWord [] else mkReZero) (makeRegExFromCharSet (\ch -> Map.lookup (q1, ch) delta == Just q2))) of
                    ReZero -> ((q1, q2), Nothing)
                    re -> ((q1, q2), Just re)
                | q1 <- qs
                , q2 <- qs
                ]
            loop :: ParserS -> Map.Map (ParserS, ParserS) RegEx -> Map.Map (ParserS, ParserS) RegEx
            loop q prev = fromMaybeList
                [ case reduceRegEx (mkReUnion (prev `lookTable` (q1, q2)) (mkReConcat (prev `lookTable` (q1, q)) (mkReConcat (mkReStar (prev `lookTable` (q, q))) (prev `lookTable` (q, q2))))) of
                    ReZero -> ((q1, q2), Nothing)
                    re -> ((q1, q2), Just re)
                | q1 <- qs
                , q2 <- qs
                ]
            fromMaybeList :: Ord k => [(k, Maybe a)] -> Map.Map k a
            fromMaybeList pairs = Map.fromList [ mkstrict (k, a) | (k, Just a) <- pairs ]

generateRegexTable :: DFA -> Map.Map ParserS RegEx
generateRegexTable dfa = result where
    qs :: [ParserS]
    qs = Set.toAscList (Set.map fst (Map.keysSet (getTransitionsOfDFA dfa)) `Set.union` Map.keysSet (getFinalQsOfDFA dfa))
    theJumpRegexTable :: Map.Map (ParserS, ParserS) RegEx
    theJumpRegexTable = makeJumpRegexTable dfa
    result :: Map.Map ParserS RegEx
    result = Map.fromAscList
        [ mkstrict
            ( q
            , theJumpRegexTable Map.! (getInitialQOfDFA dfa, q)
            )
        | q <- qs
        ]

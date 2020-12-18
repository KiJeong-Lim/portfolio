module LGS.Show where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base
import LGS.Make
import LGS.Util

instance Show NFA where
    showsPrec _ (NFA q0 qfs deltas markeds) = strcat
        [ strstr "NFA" . nl
        , strstr "    { getInitialQOfNFA = " . showsPrec 0 q0 . nl
        , strstr "    , getFinalQsOfNFA = XSet.fromAscList [" . ppunc ", " (map (showsPrec 0) (Set.toAscList qfs)) . strstr "]" . nl
        , strstr "    , getTransitionsOfNFA = XMap.fromAscList " . plist 8 [ strstr "((" . showsPrec 0 (fst key) . strstr ", " . showsPrec 0 (snd key) . strstr "), XSet.fromAscList [" . ppunc ", " [ showsPrec 0 q | q <- Set.toAscList qs ] . strstr "])" | (key, qs) <- Map.toAscList deltas ] . nl
        , strstr "    , getMarkedQsOfNFA = XMap.fromAscList [" . ppunc ", " [ strstr "(" . showsPrec 0 q . strstr ", " . showsPrec 0 p . strstr ")" | (q, p) <- Map.toAscList markeds ] . strstr "]" . nl
        , strstr "    }"
        ]
    showList = undefined

instance Show DFA where
    showsPrec _ (DFA q0 qfs deltas markeds) = strcat
        [ strstr "DFA" . nl
        , strstr "    { getInitialQOfDFA = " . showsPrec 0 q0 . nl
        , strstr "    , getFinalQsOfDFA = XMap.fromAscList [" . ppunc ", " [ strstr "(" . showsPrec 0 q . strstr ", " . showsPrec 0 p . strstr ")" | (q, p) <- Map.toAscList qfs ] . strstr "]" . nl
        , strstr "    , getTransitionsOfDFA = XMap.fromAscList " . plist 8 [ ppunc ", " [ strstr "((" . showsPrec 0 q . strstr ", " . showsPrec 0 ch . strstr "), " . showsPrec 0 p . strstr ")" | ((q, ch), p) <- deltas ] | deltas <- split' (\x1 -> \x2 -> fst (fst x1) == fst (fst x2)) (Map.toAscList deltas) ] . nl
        , strstr "    , getMarkedQsOfDFA = XMap.fromAscList " . plist 8 [ strstr "(" . showsPrec 0 q . strstr ", XSet.fromAscList [" . ppunc ", " [ showsPrec 0 p | p <- Set.toAscList ps ] . strstr "])" | (q, ps) <- Map.toAscList markeds ] . nl
        , strstr "    }"
        ]
    showList = undefined

modifyCSinRE :: (CharSet -> ExceptT ErrMsg Identity CharSet) -> (RegEx -> ExceptT ErrMsg Identity RegEx)
modifyCSinRE modify = go where
    go :: RegEx -> ExceptT ErrMsg Identity RegEx
    go (ReVar var) = pure (ReVar var)
    go ReZero = pure ReZero
    go (regex1 `ReUnion` regex2) = pure ReUnion <*> go regex1 <*> go regex2
    go (ReWord word) = pure (ReWord word)
    go (regex1 `ReConcat` regex2) = pure ReConcat <*> go regex1 <*> go regex2
    go (ReStar regex1) = pure ReStar <*> go regex1
    go (ReDagger regex1) = pure ReDagger <*> go regex1
    go (ReQuest regex1) = pure ReQuest <*> go regex1
    go (ReCharSet chs) = pure ReCharSet <*> modify chs

substituteCS :: CharSetEnv -> CharSet -> ExceptT ErrMsg Identity CharSet
substituteCS env = go where
    go :: CharSet -> ExceptT ErrMsg Identity CharSet
    go (CsVar var) = maybe (throwE ("`Src.Generator.Lexical.substituteCS\': couldn't find the variable ``$" ++ var ++ "\'\' in the environment `" ++ show env ++ "\'.")) return (Map.lookup var env)
    go (CsSingle ch) = pure (CsSingle ch)
    go (CsEnum ch1 ch2) = pure (CsEnum ch1 ch2)
    go (chs1 `CsUnion` chs2) = pure CsUnion <*> go chs1 <*> go chs2
    go (chs1 `CsDiff` chs2) = pure CsDiff <*> go chs1 <*> go chs2
    go CsUniv = pure CsUniv

substituteRE :: RegExEnv -> RegEx -> ExceptT ErrMsg Identity RegEx
substituteRE env = go where
    go :: RegEx -> ExceptT ErrMsg Identity RegEx
    go (ReVar var) = maybe (throwE ("`Src.Generator.Lexical.substituteRE\': couldn't find the variable ``$" ++ var ++ "\'\' in the environment `" ++ show env ++ "\'.")) return (Map.lookup var env)
    go ReZero = pure ReZero
    go (regex1 `ReUnion` regex2) = pure ReUnion <*> go regex1 <*> go regex2
    go (ReWord word) = pure (ReWord word)
    go (regex1 `ReConcat` regex2) = pure ReConcat <*> go regex1 <*> go regex2
    go (ReStar regex1) = pure ReStar <*> go regex1
    go (ReDagger regex1) = pure ReDagger <*> go regex1
    go (ReQuest regex1) = pure ReQuest <*> go regex1
    go (ReCharSet chs) = pure (ReCharSet chs)

genLexer :: [XBlock] -> ExceptT ErrMsg Identity (String -> String)
genLexer xblocks = do
    (_, chs_env) <- flip runStateT Map.empty $ sequence
        [ do
            env <- get
            chs' <- lift (substituteCS env chs)
            put (Map.insert var chs' env)
        | CsVDef var chs <- xblocks
        ]
    (_, re_env) <- flip runStateT Map.empty $ sequence
        [ do
            env <- get
            re' <- lift (substituteRE env re)
            put (Map.insert var re' env)
        | ReVDef var re <- xblocks
        ]
    theDFA <- fmap makeDFAfromREs $ sequence
        [ case regexes of
            (regex1, Nothing) -> do
                regex1' <- substituteRE re_env regex1
                regex1'' <- modifyCSinRE (substituteCS chs_env) regex1'
                return (regex1'', Nothing)
            (regex1, Just regex2) -> do
                regex1' <- substituteRE re_env regex1
                regex1'' <- modifyCSinRE (substituteCS chs_env) regex1'
                regex2' <- substituteRE re_env regex2
                regex2'' <- modifyCSinRE (substituteCS chs_env) regex2'
                return (regex1'', Just regex2'')
        | XMatch regexes _ <- xblocks
        ]
    let maybe_head [] = Nothing
        maybe_head (x : xs) = Just x
        tellLine delta = tell [delta . nl]
    (token_type, lexer_name) <- case maybe_head [ (token_type, lexer_name) | Target token_type lexer_name <- xblocks ] of
        Nothing -> throwE "a target block required."
        Just pair -> return pair
    hshead <- case maybe_head [ hscode | HsHead hscode <- xblocks ] of
        Nothing -> throwE "a hshead block required."
        Just hscode -> return hscode
    hstail <- case maybe_head [ hscode | HsTail hscode <- xblocks ] of
        Nothing -> throwE "a hshead block required."
        Just hscode -> return hscode
    fmap (strcat . snd) $ runWriterT $ do
        tellLine (ppunc "\n" (map strstr hshead))
        tellLine (strstr "import qualified Control.Monad.Trans.State.Strict as XState")
        tellLine (strstr "import qualified Data.Functor.Identity as XIdentity")
        tellLine (strstr "import qualified Data.Map.Strict as XMap")
        tellLine (strstr "import qualified Data.Set as XSet")
        tellLine (strstr "")
        tellLine (strstr "data DFA")
        tellLine (strstr "    = DFA")
        tellLine (strstr "        { getInitialQOfDFA :: Int")
        tellLine (strstr "        , getFinalQsOfDFA :: XMap.Map Int Int")
        tellLine (strstr "        , getTransitionsOfDFA :: XMap.Map (Int, Char) Int")
        tellLine (strstr "        , getMarkedQsOfDFA :: XMap.Map Int (XSet.Set Int)")
        tellLine (strstr "        }")
        tellLine (strstr "    deriving ()")
        tellLine (strstr "")
        tellLine (ppunc "\n" (map strstr hstail))
        tellLine (strstr "")
        tellLine (strstr lexer_name . strstr " :: String -> Either (Int, Int) [" . strstr token_type . strstr "]")
        tellLine (strstr lexer_name . strstr " = doLexing . addLoc 1 1 where")
        tellLine (strstr "    theDFA :: DFA")
        tellLine (strstr "    theDFA = DFA")
        tellLine (strstr "        { getInitialQOfDFA = " . showsPrec 0 (getInitialQOfDFA theDFA))
        tellLine (strstr "        , getFinalQsOfDFA = XMap.fromAscList [" . ppunc ", " [ strstr "(" . showsPrec 0 q . strstr ", " . showsPrec 0 p . strstr ")" | (q, p) <- Map.toAscList (getFinalQsOfDFA theDFA) ] . strstr "]")
        tellLine (strstr "        , getTransitionsOfDFA = XMap.fromAscList " . plist 8 [ ppunc ", " [ strstr "((" . showsPrec 0 q . strstr ", " . showsPrec 0 ch . strstr "), " . showsPrec 0 p . strstr ")" | ((q, ch), p) <- deltas ] | deltas <- split' (\x1 -> \x2 -> fst (fst x1) == fst (fst x2)) (Map.toAscList (getTransitionsOfDFA theDFA)) ])
        tellLine (strstr "        , getMarkedQsOfDFA = XMap.fromAscList " . plist 8 [ strstr "(" . showsPrec 0 q . strstr ", XSet.fromAscList [" . ppunc ", " [ showsPrec 0 p | p <- Set.toAscList ps ] . strstr "])" | (q, ps) <- Map.toAscList (getMarkedQsOfDFA theDFA) ])
        tellLine (strstr "        }")
        tellLine (strstr "    runDFA :: DFA -> (ch -> Char) -> [ch] -> ((Maybe Int, [ch]), [ch])")
        tellLine (strstr "    runDFA (DFA q0 qfs deltas markeds) toChar = XIdentity.runIdentity . go where")
        tellLine (strstr "        loop1 q buffer [] = return buffer")
        tellLine (strstr "        loop1 q buffer (ch : str) = do")
        tellLine (strstr "            case XMap.lookup (q, toChar ch) deltas of")
        tellLine (strstr "                Nothing -> return (buffer ++ [ch] ++ str)")
        tellLine (strstr "                Just p -> case XMap.lookup p qfs of")
        tellLine (strstr "                    Nothing -> loop1 p (buffer ++ [ch]) str")
        tellLine (strstr "                    latest' -> do")
        tellLine (strstr "                        (latest, accepted) <- XState.get")
        tellLine (strstr "                        XState.put (latest', accepted ++ buffer ++ [ch])")
        tellLine (strstr "                        loop1 p [] str")
        tellLine (strstr "        loop2 qs q [] buffer = return buffer")
        tellLine (strstr "        loop2 qs q (ch : str) buffer = do")
        tellLine (strstr "            case XMap.lookup (q, toChar ch) deltas of")
        tellLine (strstr "                Nothing -> return (buffer ++ [ch] ++ str)")
        tellLine (strstr "                Just p -> case p `XSet.member` qs of")
        tellLine (strstr "                    False -> loop2 qs p str (buffer ++ [ch])")
        tellLine (strstr "                    True -> do")
        tellLine (strstr "                        accepted <- XState.get")
        tellLine (strstr "                        XState.put (accepted ++ buffer ++ [ch])")
        tellLine (strstr "                        loop2 qs p str []")
        tellLine (strstr "        go input = do")
        tellLine (strstr "            (rest, (latest, accepted)) <- XState.runStateT (loop1 q0 [] input) (Nothing, [])")
        tellLine (strstr "            case latest >>= flip XMap.lookup markeds of")
        tellLine (strstr "                Nothing -> return ((latest, accepted), rest)")
        tellLine (strstr "                Just qs -> do")
        tellLine (strstr "                    (rest', accepted') <- XState.runStateT (loop2 qs q0 accepted []) []")
        tellLine (strstr "                    return ((latest, accepted'), rest' ++ rest)")
        tellLine (strstr "    addLoc :: Int -> Int -> String -> [((Int, Int), Char)]")
        tellLine (strstr "    addLoc _ _ [] = []")
        tellLine (strstr "    addLoc row col (ch : chs) = if ch == \'\\n\' then ((row, col), ch) : addLoc (row + 1) 1 chs else ((row, col), ch) : addLoc row (col + 1) chs")
        tellLine (strstr "    doLexing :: [((Int, Int), Char)] -> Either (Int, Int) [" . strstr token_type . strstr "]")
        tellLine (strstr "    doLexing [] = return []")
        tellLine (strstr "    doLexing str0 = do")
        tellLine (strstr "        (str1, piece) <- case runDFA theDFA snd str0 of")
        tellLine (strstr "            ((_, []), _) -> Left (fst (head str0))")
        tellLine (strstr "            ((Just label, accepted), rest) -> return (rest, ((label, map snd accepted), (fst (head accepted), fst (head (reverse accepted)))))")
        tellLine (strstr "            _ -> Left (fst (head str0))")
        tellLine (strstr "        maybe_token <- case piece of")
        let destructors = [ destructor | XMatch _ destructor <- xblocks ]
        sequence
            [ case destructor of
                Nothing -> do
                    tellLine (strstr "            ((" . showsPrec 0 line . strstr ", this), ((row1, col1), (row2, col2))) -> return Nothing")
                    return ()
                Just hscode -> do
                    tellLine (strstr "            ((" . showsPrec 0 line . strstr ", this), ((row1, col1), (row2, col2))) -> return $ Just $")
                    tellLine (ppunc "\n" [ strstr "                " . strstr str | str <- hscode ])
                    return ()
            | (line, destructor) <- zip [1, 2 .. length destructors] destructors 
            ]
        tellLine (strstr "        fmap (maybe id (:) maybe_token) (doLexing str1)")
        tellLine (strstr "")

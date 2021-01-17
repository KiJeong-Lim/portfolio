module PGS.Show where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Algorithm.Sorting
import Lib.Base
import Lib.Text.PC
import Lib.Text.PC.Expansion
import PGS.Make
import PGS.Util

instance Show Conflict where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec _ (Conflict (action1, action2) (q, t) (Cannonical0 vertices root edges))
        = strcat
            [ strstr "couldn't resolve conflict:" . nl
            , strstr "  ? " . pprint 0 action1 . strstr " v.s. " . pprint 0 action2 . strstr " at (" . showsPrec 0 q . strstr ", " . showsPrec 0 (TS t) . strstr ")" . nl
            , strstr "  ? collection = Cannonical0" . nl
            , strstr "    { getVertices = " . plist 6 [ showsPrec 0 q . strstr ": " . plist 8 (map (pprint 0) items) | (q, items) <- formatedVertices ] . nl
            , strstr "    , getRoot = " . showsPrec 0 root . nl
            , strstr "    , getEdges = " . plist 6 [ showsPrec 0 q . strstr ": " . plist 8 [ pprint 0 sym . strstr " +-> " . showsPrec 0 p | (sym, p) <- pairs ] | (q, pairs) <- formatedEdges ] . nl
            , strstr "    }" . nl
            ]
        where
            formatedVertices :: [(ParserS, [LR0Item])]
            formatedVertices = do
                (items, q) <- sortByMerging (\pair1 -> \pair2 -> snd pair1 < snd pair2) (Map.toAscList vertices)
                return
                    ( q
                    , Set.toAscList items
                    )
            formatedEdges :: [(ParserS, [(Sym, ParserS)])]
            formatedEdges = do
                triples <- split' (\triple1 -> \triple2 -> fst (fst triple1) == fst (fst triple2)) (Map.toAscList edges)
                case triples of
                    [] -> []
                    ((q, sym), p) : triples' -> return
                        ( q
                        , (sym, p) : [ (sym', p') | ((q', sym'), p') <- triples' ]
                        )

unFoldNSApp :: NSym -> (String, [NSym])
unFoldNSApp = flip loop [] where
    loop :: NSym -> [NSym] -> (String, [NSym])
    loop (NSVar nsv) nss = (nsv, nss)
    loop (NSApp ns1 ns2) nss = loop ns1 (ns2 : nss)

substituteNS :: [(String, NSym)] -> NSym -> NSym
substituteNS mapsto = loop where
    loop :: NSym -> NSym
    loop (NSVar nsv) = case lookup nsv mapsto of
        Nothing -> NSVar nsv
        Just ns -> ns
    loop (NSApp ns1 ns2) = NSApp (loop ns1) (loop ns2)

makeProductionRuleInstances :: Map.Map String ([String], [YMatch]) -> NSym -> StateT ((Int, Map.Map NSym Int), Map.Map NSym (Maybe [([Sym], Precedence)])) (ExceptT ErrMsg Identity) ()
makeProductionRuleInstances rule_env = fmap (const ()) . go where
    go :: NSym -> StateT ((Int, Map.Map NSym Int), Map.Map NSym (Maybe [([Sym], Precedence)])) (ExceptT ErrMsg Identity) NSym
    go ns = do
        ((max_id_num, id_env), cache) <- get
        case unFoldNSApp ns of
            (nsv, nss) -> case Map.lookup nsv rule_env of
                Nothing -> lift (throwE ("cannot find the defintion of the scheme ``" ++ nsv ++ "\'\'."))
                Just (params, match_decls)
                    | length params /= length nss -> lift (throwE ("args do not match to params: length " ++ showList nss (" /= length " ++ showList params ".")))
                    | otherwise -> do
                        let mapsto = zip params nss
                        case Map.lookup ns id_env of
                            Nothing -> do
                                put ((max_id_num + 1, Map.insert ns max_id_num id_env), Map.insert ns Nothing cache)
                                mapM go nss
                                pairs <- sequence
                                    [ do
                                        pats' <- forM pats $ \pat -> case pat of
                                            NS ns' -> NS <$> go (substituteNS mapsto ns')
                                            _ -> return pat
                                        return (pats', prec)
                                    | YMatch prec pats destructors <- match_decls
                                    ]
                                (pair', cache') <- get
                                put (pair', Map.update (const (Just (Just pairs))) ns cache')
                            _ -> return ()
                        return (substituteNS mapsto ns)

genParser :: [YBlock] -> ExceptT ErrMsg Identity (String -> String)
genParser blocks = go where
    naturals :: [Int]
    naturals = [1, 2 .. ]
    tellLine :: (String -> String) -> WriterT [String -> String] (ExceptT String Identity) ()
    tellLine delta = tell [delta . nl]
    getYTarget :: ExceptT ErrMsg Identity YTarget
    getYTarget = case [ y_target | Target y_target <- blocks ] of
        [] -> throwE "a target block required."
        [y_target] -> return y_target
        _ -> throwE "ambiguous target blocks."
    getHsHead :: ExceptT ErrMsg Identity HsCode
    getHsHead = case [ hshead | HsHead hshead <- blocks ] of
        [] -> throwE "a hshead block required."
        [hshead] -> return hshead
        _ -> throwE "ambiguous hshead block."
    getHsTail :: ExceptT ErrMsg Identity HsCode
    getHsTail = case [ hstail | HsTail hstail <- blocks ] of
        [] -> throwE "a hstail block required."
        [hstail] -> return hstail
        _ -> throwE "ambiguous hstail block."
    checkTerminalOccurence :: Set.Set TSym -> Set.Set TSym -> ExceptT ErrMsg Identity ()
    checkTerminalOccurence subs supers
        | subs `Set.isSubsetOf` supers = return ()
        | otherwise = throwE ("definitions of the following terminal symbols required: " ++ concat [ "  " ++ show ts ++ "\n" | ts <- Set.toList (subs `Set.difference` supers) ])
    getGetRep :: NSym -> String -> String
    getGetRep = go 0 where
        go :: Int -> NSym -> String -> String
        go 0 (NSApp ns1 ns2) = go 0 ns1 . strstr " " . go 1 ns2
        go 0 ns = go 1 ns
        go 1 (NSVar nsv) = strstr "get" . strstr nsv
        go 1 ns = go 2 ns
        go _ ns = strstr "(" . go 0 ns . strstr ")"
    patTsIdx :: Int -> String -> String -> String
    patTsIdx idx field = strstr field . strstr "_" . showsPrec 0 idx
    patNsIdx :: Int -> String -> String
    patNsIdx idx = strstr "_" . showsPrec 0 idx
    makeNSPatn :: Int -> String -> String
    makeNSPatn idx = strcat
        [ patNsIdx idx
        , strstr "@(PTBranch "
        , guardIdx idx
        , strstr " "
        , strstr "_"
        , strstr ")"
        ]
    makeTSPatn :: Map.Map TSym String -> Int -> TSym -> String -> String
    makeTSPatn mapTSymToPatn = loop where
        acceptSmallId :: PC String
        acceptSmallId = regexPC "['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*"
        makePatn :: Int -> PC (String -> String)
        makePatn idx = fmap strcat $ many $ mconcat
            [ do
                field <- acceptSmallId
                return (patTsIdx idx field)
            , do
                quote <- acceptQuote
                return (showsPrec 0 quote)
            , do
                negPC (acceptSmallId <|> acceptQuote)
                hs_src <- some (acceptPC (\ch -> ch /= ' '))
                return (strstr hs_src)
            , do
                ch <- acceptPC (\ch -> ch == ' ')
                return (strstr [ch])
            ]
        loop :: Int -> TSym -> String -> String
        loop idx tsym = case Map.lookup tsym mapTSymToPatn of
            Nothing -> error "`makeTSPatn\'"
            Just patn -> strstr "PTLeaf (" . either (error "`makeTSPatn\'") id (runPC (makePatn idx) patn) . strstr ")"
    guardIdx :: Int -> String -> String
    guardIdx idx = strstr "guard" . showsPrec 0 idx
    makeGuard :: Map.Map NSym Int -> String -> [String] -> [(Int, Sym)] -> String -> String
    makeGuard id_env body_name params_name zipped_sym = if null [ (idx, ns) | (idx, NS ns) <- zipped_sym ] then strstr "otherwise" else guard where
        guard :: String -> String
        guard = strcat
            [ strstr "["
            , ppunc ", " [ guardIdx idx | (idx, NS ns) <- zipped_sym ]
            , strstr "] `elem` ["
            , ppunc ", "
                [ strcat
                    [ strstr "["
                    , ppunc ", "
                        [ case Map.lookup (substituteNS (zip params_name (snd (unFoldNSApp ns1))) ns) id_env of
                            Nothing -> error "makeGuard"
                            Just num -> showsPrec 0 num
                        | (idx, NS ns) <- zipped_sym
                        ]
                    , strstr "]"
                    ]
                | (ns1, num1) <- Map.toList id_env
                , body_name == fst (unFoldNSApp ns1)
                ]
            , strstr "]"
            ]
    formatTable :: Ord a => [((a, b), c)] -> [(a, [(b, c)])]
    formatTable = sortByMerging (\pair1 -> \pair2 -> fst pair1 <= fst pair2) . loop where
        loop :: Eq a => [((a, b), c)] -> [(a, [(b, c)])]
        loop [] = []
        loop (((x, y), z) : triples) = case List.partition (\triple -> fst (fst triple) == x) triples of
            (triples1, triples2) -> (x, (y, z) : [ (y, z) | ((_, y), z) <- triples1 ]) : loop triples2
    go :: ExceptT ErrMsg Identity (String -> String)
    go = do
        hs_head <- getHsHead
        hs_tail <- getHsTail
        y_target <- getYTarget
        let token_type = getTokenType y_target
            parser_name = getParserName y_target
            result_type = getResultType y_target
            start_symbol = getStartSymbol y_target
            terminal_infos = getTerminalInfos y_target
            rule_env = Map.fromList
                [ case (fst body, fst (unzip params)) of
                    (body_name, params_name) -> (body_name, (params_name, match_decls))
                | Define (Scheme type_constraint body params match_decls) <- blocks
                ]
        ((), ((max_id_num, id_env), cache)) <- runStateT (makeProductionRuleInstances rule_env start_symbol) ((1, Map.empty), Map.empty)
        let cache' = Map.toList cache
            production_rules = Map.fromList
                [ ((lhs, rhs), prec)
                | (lhs, Just pairs) <- cache'
                , (rhs, prec) <- pairs
                ]
            terminal_symbols = Map.fromList
                [ (tsym, (assoc, prec))
                | TerminalInfo patn tsym prec assoc <- terminal_infos
                ]
            getTSymId TSEOF = return 0
            getTSymId (TSVar tsv) = case [ n | (n, TerminalInfo patn ts prec assoc) <- zip naturals terminal_infos, ts == TSVar tsv ] of
                [] -> throwE ("the terminal symbol " ++ pprint 0 (TSVar tsv) " hasn't declared.")
                [n] -> return n
                _ -> throwE ("the terminal symbol " ++ pprint 0 (TSVar tsv) " has declared twice or more.")
            getNSymId nsym = case Map.lookup nsym id_env of
                Nothing -> throwE ("the terminal symbol " ++ pprint 0 nsym " hasn't declared.")
                Just n -> return n
        checkTerminalOccurence (Set.fromList [ ts | (lhs, Just pairs) <- cache', (rhs, prec) <- pairs, TS ts <- rhs ]) (Set.fromList [ tsym | TerminalInfo patn tsym prec assoc <- terminal_infos ])
        (collection, lalr1) <- catchE (makeCollectionAndLALR1Parser (CFGrammar { getStartSym = start_symbol, getTerminalSyms = terminal_symbols, getProductionRules = production_rules })) $ throwE . show
        fmap (strcat . snd) $ runWriterT $ do
            tellLine (ppunc "\n" (map strstr hs_head))
            tellLine (strstr "import qualified Control.Monad.Trans.Class as Y")
            tellLine (strstr "import qualified Control.Monad.Trans.Except as Y")
            tellLine (strstr "import qualified Control.Monad.Trans.State.Strict as Y")
            tellLine (strstr "import qualified Data.Map.Strict as YMap")
            tellLine (strstr "import qualified Data.Set as YSet")
            tellLine (strstr "")
            tellLine (strstr "type ParserS = Int")
            tellLine (strstr "")
            tellLine (strstr "type NSym = Int")
            tellLine (strstr "")
            tellLine (strstr "type TSym = Int")
            tellLine (strstr "")
            tellLine (strstr "data Sym")
            tellLine (strstr "    = NS NSym")
            tellLine (strstr "    | TS TSym")
            tellLine (strstr "    deriving (Eq, Ord)")
            tellLine (strstr "")
            tellLine (strstr "data Action")
            tellLine (strstr "    = Shift ParserS")
            tellLine (strstr "    | Reduce (NSym, [Sym])")
            tellLine (strstr "    | Accept")
            tellLine (strstr "    deriving (Eq)")
            tellLine (strstr "")
            tellLine (strstr "data LR1Parser")
            tellLine (strstr "    = LR1Parser")
            tellLine (strstr "        { getInitialS :: ParserS")
            tellLine (strstr "        , getActionTable :: YMap.Map (ParserS, TSym) Action")
            tellLine (strstr "        , getReduceTable :: YMap.Map (ParserS, NSym) ParserS")
            tellLine (strstr "        }")
            tellLine (strstr "    deriving ()")
            tellLine (strstr "")
            tellLine (strstr "data ParsingTree")
            tellLine (strstr "    = PTLeaf (" . strstr token_type . strstr ")")
            tellLine (strstr "    | PTBranch NSym [ParsingTree]")
            tellLine (strstr "    deriving ()")
            tellLine (strstr "")
            tellLine (ppunc "\n" (map strstr hs_tail))
            tellLine (strstr "-- the following codes are generated by PGS.")
            tellLine (strstr "")
            tellLine (strstr parser_name . strstr " :: [" . strstr token_type . strstr "] -> Either (Maybe (" . strstr token_type . strstr ")) (" . strstr result_type . strstr ")")
            tellLine (strstr parser_name . strstr " = fmap (" . getGetRep start_symbol . strstr ") . runLR1 theLR1Parser where")
            sequence
                [ do
                    let body_name = fst body
                        body_type = snd body
                        params_name = fst (unzip params)
                        params_type = snd (unzip params)
                    tellLine $ strcat
                        [ strstr "    get"
                        , strstr body_name
                        , strstr " :: "
                        , strstr (maybe "" (\type_ctx -> type_ctx ++ " => ") type_constraint)
                        , foldr (\arg_typ -> \acc -> strstr "(ParsingTree -> (" . strstr arg_typ . strstr ")) -> " . acc) (strstr "ParsingTree -> (" . strstr body_type . strstr ")") params_type
                        ]
                    sequence
                        [ do
                            tellLine $ strcat
                                [ strstr "    get"
                                , strstr body_name
                                , strcat [ strstr " get" . strstr param_name | param_name <- params_name ]
                                , strstr " (PTBranch _ ["
                                , ppunc ", "
                                    [ case sym of
                                        NS ns -> makeNSPatn idx
                                        TS ts -> makeTSPatn (Map.fromList [ (tsym, patn) | TerminalInfo patn tsym _ _ <- terminal_infos ]) idx ts
                                    | (idx, sym) <- zip naturals syms
                                    ]
                                , strstr "])"
                                ]
                            sequence
                                [ do
                                    let mkIndexErr idx = "the length of rhs is " ++ showsPrec 0 (length syms) (", but the index " ++ showsPrec 0 idx " is greater than or equal to it.")
                                    des_rep <- fmap (ppunc  "        ") $ sequence
                                        [ lift $ fmap strcat $ sequence
                                            [ case de of
                                                DsStrLit str -> return (showsPrec 0 str)
                                                DsSource hs_src -> return (strstr hs_src)
                                                DsNSPatn idx
                                                    | idx <= length syms -> case syms !! (idx - 1) of
                                                        NS ns -> return (strstr "(" . getGetRep ns . strstr " " . patNsIdx idx . strstr ")")
                                                        TS ts -> throwE ("a DsTSPatn must be matched to a nonterminal symbol.")
                                                    | otherwise -> throwE (mkIndexErr idx)
                                                DsTSPatn idx field
                                                    | idx <= length syms -> case syms !! (idx - 1) of
                                                        NS ns -> throwE ("a DsTSPatn must be matched to a terminal symbol.")
                                                        TS ts -> return (strstr "(" . patTsIdx idx field . strstr ")")
                                                    | otherwise -> throwE (mkIndexErr idx)
                                            | de <- des
                                            ]
                                        ]
                                    tellLine $ strcat
                                        [ strstr "        | "
                                        , makeGuard id_env body_name params_name (zip naturals syms)
                                        , strstr " = "
                                        , des_rep
                                        ]
                                    return ()
                                | des <- dess
                                ]
                            return ()
                        | YMatch prec syms dess <- match_decls
                        ]
                    return ()
                | Define (Scheme type_constraint body params match_decls) <- blocks
                ]
            tellLine (strstr "    toTerminal :: (" . strstr token_type . strstr ") -> TSym")
            sequence
                [ do
                    tsym_id <- lift (getTSymId tsym)
                    tellLine (strstr "    toTerminal (" . strstr patn . strstr ") = " . showsPrec 0 tsym_id)
                | TerminalInfo patn tsym prec assoc <- terminal_infos
                ]
            tellLine (strstr "    runLR1 :: LR1Parser -> [" . strstr token_type . strstr "] -> Either (Maybe (" . strstr token_type . strstr ")) ParsingTree")
            tellLine (strstr "    runLR1 (LR1Parser getInitS getActionT getReduceT) = go where")
            tellLine (strstr "        loop inputs = do")
            tellLine (strstr "            let cur = if null inputs then 0 else toTerminal (head inputs)")
            tellLine (strstr "                exception = Y.lift (if null inputs then Left Nothing else Left (Just (head inputs)))")
            tellLine (strstr "            (stack, trees) <- Y.get")
            tellLine (strstr "            case YMap.lookup (head stack, cur) getActionT of")
            tellLine (strstr "                Nothing -> exception")
            tellLine (strstr "                Just Accept -> return ()")
            tellLine (strstr "                Just (Shift top') -> do")
            tellLine (strstr "                    Y.put (top' : stack, PTLeaf (head inputs) : trees)")
            tellLine (strstr "                    loop (tail inputs)")
            tellLine (strstr "                Just (Reduce (lhs, rhs)) -> do")
            tellLine (strstr "                    let n = length rhs")
            tellLine (strstr "                    case YMap.lookup (stack !! n, lhs) getReduceT of")
            tellLine (strstr "                        Nothing -> exception")
            tellLine (strstr "                        Just top' -> do")
            tellLine (strstr "                            Y.put (top' : drop n stack, PTBranch lhs (reverse (take n trees)) : drop n trees)")
            tellLine (strstr "                            loop inputs")
            tellLine (strstr "        go tokens = do")
            tellLine (strstr "            (_, (_, result)) <- Y.runStateT (loop tokens) ([getInitS], [])")
            tellLine (strstr "            case result of")
            tellLine (strstr "                [output] -> return output")
            tellLine (strstr "    theLR1Parser :: LR1Parser")
            tellLine (strstr "    theLR1Parser = LR1Parser")
            tellLine (strstr "        { getInitialS = " . showsPrec 0 (getInitialS lalr1))
            action_table_rep <- lift $ sequence
                [ fmap (ppunc ", ") $ do
                    pairs' <- sequence
                        [ do
                            tsym_id <- getTSymId tsym
                            return (tsym_id, action)
                        | (tsym, action) <- pairs
                        ]
                    sequence
                        [ case action of
                            Shift p -> return $ strcat
                                [ strstr "(("
                                , showsPrec 0 q
                                , strstr ", "
                                , showsPrec 0 tsym_id
                                , strstr "), Shift "
                                , showsPrec 0 p
                                , strstr ")"
                                ]
                            Reduce (lhs, rhs) -> do
                                lhs_rep <- getNSymId lhs
                                rhs_rep <- sequence
                                    [ case sym of
                                        NS ns -> do
                                            ns_rep <- getNSymId ns
                                            return (strstr "NS " . showsPrec 0 ns_rep)
                                        TS ts -> do
                                            ts_rep <- getTSymId ts
                                            return (strstr "TS " . showsPrec 0 ts_rep)
                                    | sym <- rhs
                                    ]
                                return $ strcat
                                    [ strstr "(("
                                    , showsPrec 0 q
                                    , strstr ", "
                                    , showsPrec 0 tsym_id
                                    , strstr "), Reduce ("
                                    , showsPrec 0 lhs_rep
                                    , strstr ", ["
                                    , ppunc ", " rhs_rep
                                    , strstr "]))"
                                    ]
                            Accept -> return $ strcat
                                [ strstr "(("
                                , showsPrec 0 q
                                , strstr ", "
                                , showsPrec 0 tsym_id
                                , strstr "), Accept)"
                                ]
                        | (tsym_id, action) <- sortByMerging (\pair1 -> \pair2 -> fst pair1 <= fst pair2) pairs'
                        ]
                | (q, pairs) <- formatTable (Map.toAscList (getActionTable lalr1))
                ]
            tellLine (strstr "        , getActionTable = YMap.fromAscList " . plist 12 action_table_rep)
            table2 <- lift $ sequence
                [ fmap (ppunc ", ") $ do
                    pairs' <- sequence
                        [ do
                            nsym_id <- getNSymId nsym
                            return (nsym_id, p)
                        | (nsym, p) <- pairs
                        ]
                    return
                        [ strcat
                            [ strstr "(("
                            , showsPrec 0 q
                            , strstr ", "
                            , showsPrec 0 nsym_id
                            , strstr "), "
                            , showsPrec 0 p
                            , strstr ")"
                            ]
                        | (nsym_id, p) <- sortByMerging (\pair1 -> \pair2 -> fst pair1 <= fst pair2) pairs'
                        ]
                | (q, pairs) <- formatTable (Map.toAscList (getReduceTable lalr1))
                ]
            tellLine (strstr "        , getReduceTable = YMap.fromAscList " . plist 12 table2)
            tellLine (strstr "        }")
            tellLine (strstr "")
            tellLine (strstr "{- The canonical collection of LR(0) items is:" . nl . pprint 0 collection . nl . strstr "-}")
            return ()

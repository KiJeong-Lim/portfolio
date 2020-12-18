module PGS.Make where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base
import PGS.Util

instance Outputable Associativity where
    makeOutput _ ALeft = strstr "left"
    makeOutput _ ARight = strstr "right"
    makeOutput _ ANone = strstr "none"

instance Outputable NSym where
    makeOutput 0 (NSApp ns1 ns2) = makeOutput 0 ns1 . strstr " " . makeOutput 1 ns2
    makeOutput 0 ns1 = makeOutput 1 ns1
    makeOutput 1 (NSVar nsv) = strstr nsv
    makeOutput 1 ns1 = makeOutput 2 ns1
    makeOutput _ ns1 = strstr "(" . makeOutput 0 ns1 . strstr ")"

instance Outputable TSym where
    makeOutput _ (TSEOF) = strstr "\\$"
    makeOutput _ (TSVar tsv) = strstr tsv

instance Outputable Sym where
    makeOutput _ (NS ns) = strstr "<" . makeOutput 0 ns . strstr ">"
    makeOutput _ (TS ts) = strstr "`" . makeOutput 0 ts . strstr "\'"

instance Outputable CFGrammar where
    makeOutput _ (CFGrammar start terminals productions) = strcat
        [ strstr "start-symbol: " . makeOutput 0 start . nl
        , strstr "terminal-symbols: " . plist 2 [ makeOutput 0 (TS t) . strstr " : " . makeOutput 0 assoc . strstr ", " . strstr (reverse (take 2 ("0" ++ reverse (show prec)))) | (t, (assoc, prec)) <- Map.toList terminals ] . nl
        , strstr "production-rules: " . plist 2 [ makeOutput 0 (NS lhs) . strstr " ::= " . ppunc " " (map (makeOutput 0) rhs) . strstr "; " . strstr (reverse (take 2 (reverse ("0" ++ show prec)))) | ((lhs, rhs), prec) <- Map.toList productions ] . nl
        ]

instance Outputable LR0Item where
    makeOutput _ (LR0Item lhs left right) = makeOutput 0 (NS lhs) . strstr " ::= " . ppunc " " (map (makeOutput 0) left) . strstr " . " . ppunc " " (map (makeOutput 0) right) . strstr ";"

instance Outputable Cannonical0 where
    makeOutput _ (Cannonical0 vertices root edges) = strcat
        [ strstr "vertices: " . plist 2 [ showsPrec 0 q . strstr ": " . plist 4 (map (makeOutput 0) (Set.toList items)) | (items, q) <- Map.toList vertices ] . nl
        , strstr "root: " . showsPrec 0 root . nl
        , strstr "edges: " . plist 2 [ strstr "(" . showsPrec 0 q . strstr ", " . makeOutput 0 sym . strstr ") +-> " . showsPrec 0 p | ((q, sym), p) <- Map.toList edges ] . nl
        ]

instance Outputable Action where
    makeOutput _ (Shift p) = strstr "SHIFT: " . showsPrec 0 p . strstr ";"
    makeOutput _ (Reduce (lhs, rhs)) = strstr "REDUCE: <" . makeOutput 0 lhs . strstr "> ::= " . ppunc " " (map (makeOutput 0) rhs) . strstr ";"
    makeOutput _ (Accept) = strstr "ACCEPT;"

instance Outputable LR1Parser where
    makeOutput _ (LR1Parser initS actionT reduceT) = strcat
        [ strstr "initS: " . showsPrec 0 initS . nl
        , strstr "actionT: " . plist 2 [ strstr "(" . showsPrec 0 q . strstr ", " . makeOutput 0 (TS t) . strstr ") +-> " . makeOutput 0 action | ((q, t), action) <- Map.toList actionT ] . nl
        , strstr "reduceT: " . plist 2 [ strstr "(" . showsPrec 0 q . strstr ", " . makeOutput 0 (NS nt) . showsPrec 0 p . strstr ";" | ((q, nt), p) <- Map.toList reduceT ] . nl
        ]

getLALR1 :: CFGrammar -> ExceptT String Identity LR1Parser
getLALR1 (CFGrammar start terminals productions) = makeLALR1 where
    maxPrec :: Precedence
    maxPrec = 100
    start' :: NSym
    start' = NSVar "$\\ACCEPT"
    terminals' :: Map.Map TSym (Associativity, Precedence)
    terminals' = Map.insert TSEOF (ANone, maxPrec) terminals
    productions' :: Map.Map ProductionRule Precedence
    productions' = Map.insert (start', [NS start, TS TSEOF]) maxPrec productions
    getMarkSym :: LR0Item -> Maybe Sym
    getMarkSym item = case getRIGHT item of
        [] -> Nothing
        sym : syms -> Just sym
    getCannonical0 :: Cannonical0
    getCannonical0 = runIdentity makeCannonical0 where
        getClosure :: Set.Set LR0Item -> Identity (Set.Set LR0Item)
        getClosure items = if items == items' then return items' else getClosure items' where
            items' :: Set.Set LR0Item
            items' = foldr Set.insert items
                [ LR0Item lhs [] rhs
                | ((lhs, rhs), prec) <- Map.toList productions'
                , any (\item -> getMarkSym item == Just (NS lhs)) (Set.toList items)
                ]
        getGOTO :: (Set.Set LR0Item, Sym) -> Identity (Set.Set LR0Item)
        getGOTO (items, sym)
            | sym == TS TSEOF = return Set.empty
            | otherwise = getClosure $ Set.fromList
                [ LR0Item lhs (left ++ [sym']) right
                | LR0Item lhs left (sym' : right) <- Set.toList items
                , sym == sym'
                ]
        loop :: Cannonical0 -> Identity Cannonical0
        loop collection = do
            (_, collection') <- flip runStateT collection $ sequence
                [ do
                    cl <- lift (getClosure items)
                    sequence
                        [ do 
                            items' <- lift (getGOTO (items, sym))
                            Cannonical0 vertices root edges <- get
                            if Set.null items'
                                then return () 
                                else case Map.lookup items' vertices of
                                    Nothing -> do
                                        let p = Map.size vertices
                                        put (Cannonical0 (Map.insert items' p vertices) root (Map.insert (q, sym) p edges))
                                    Just p -> put (Cannonical0 vertices root (Map.insert (q, sym) p edges))
                        | Just sym <- Set.toList (Set.map getMarkSym cl)
                        ]
                | (items, q) <- Map.toList (getVertices collection)
                ]
            if collection == collection'
                then return collection'
                else loop collection'
        makeCannonical0 :: Identity Cannonical0
        makeCannonical0 = do
            items0 <- getClosure (Set.singleton (LR0Item start' [] [NS start, TS TSEOF]))
            loop (Cannonical0 (Map.singleton items0 0) 0 Map.empty)
    getFIRST :: Map.Map NSym TerminalSet
    getFIRST = loop init where
        init :: Map.Map NSym TerminalSet
        init = Map.fromAscList
            [ (lhs, TerminalSet Set.empty)
            | ((lhs, _), _) <- Map.toAscList productions'
            ]
        loop :: Map.Map NSym TerminalSet -> Map.Map NSym TerminalSet
        loop mapping = if mapping == mapping' then mapping' else loop mapping' where
            getFirstOf :: Sym -> TerminalSet
            getFirstOf (NS ns) = case Map.lookup ns mapping of
                Nothing -> error "getLALR1.getFIRST.loop.getFirstOf"
                Just tss -> tss
            getFirstOf (TS ts) = TerminalSet (Set.singleton (Just ts))
            go :: (NSym, [Sym]) -> TerminalSet -> Maybe TerminalSet
            go (lhs, rhs) tss = Just (TerminalSet (unTerminalSet tss `Set.union` unTerminalSet (mconcat [ getFirstOf sym | sym <- rhs ])))
            mapping' :: Map.Map NSym TerminalSet
            mapping' = foldr (Map.update <$> go <*> fst) mapping (map fst (Map.toList productions'))
    getLATable :: [((ParserS, TSym), ProductionRule)]
    getLATable = runIdentity makeLATable where
        getGOTO' :: ParserS -> [Sym] -> Maybe ParserS
        getGOTO' q [] = Just q
        getGOTO' q (sym : syms) = case Map.lookup (q, sym) (getEdges getCannonical0) of
            Nothing -> Nothing
            Just p -> getGOTO' p syms
        getFirstOf :: [Sym] -> TerminalSet
        getFirstOf [] = mempty
        getFirstOf (NS ns : syms) = case Map.lookup ns getFIRST of
            Nothing -> error "getLALR1.getLATable.getFirstOf"
            Just tss -> tss <> getFirstOf syms
        getFirstOf (TS ts : _) = TerminalSet (Set.singleton (Just ts))
        getLA :: Bool -> (LR0Item, ParserS) -> StateT (Map.Map (LR0Item, ParserS) (Bool, TerminalSet)) Identity TerminalSet
        getLA final (LR0Item lhs left right, q)
            | lhs == start' = return (TerminalSet (Set.singleton (Just TSEOF)))
            | otherwise = do
                mapping <- get
                case Map.lookup (LR0Item lhs left right, q) mapping of
                    Just (correct, tss)
                        | correct || not final -> return tss
                    _ -> do
                        put (Map.insert (LR0Item lhs left right, q) (False, TerminalSet Set.empty) mapping)
                        result' <- fmap (TerminalSet . Set.unions) $ sequence
                            [ fmap Set.unions $ sequence
                                [ case getFirstOf right' of
                                    TerminalSet tss
                                        | Nothing `Set.member` tss -> do
                                            result <- getLA False (LR0Item lhs' left' (sym' : right'), p)
                                            return (Set.union (Set.delete Nothing tss) (unTerminalSet result))
                                        | otherwise -> return tss
                                | LR0Item lhs' left' (sym' : right') <- Set.toList items'
                                , sym' == NS lhs
                                ]
                            | (items', p) <- Map.toList (getVertices getCannonical0)
                            , getGOTO' p left == Just q
                            ]
                        mapping' <- get
                        put (Map.update (const (Just (final, result'))) (LR0Item lhs left right, q) mapping')
                        return result'
        makeLATable :: Identity [((ParserS, TSym), ProductionRule)]
        makeLATable = do
            (triples, _) <- flip runStateT Map.empty $ sequence
                [ do
                    ts <- getLA True (item, q)
                    return ((item, q), ts)
                | (items, q) <- Map.toList (getVertices getCannonical0)
                , item <- Set.toList items
                , getMarkSym item `elem` [Nothing, Just (TS TSEOF)]
                ]
            return
                [ ((q, t), (lhs, left ++ right))
                | ((LR0Item lhs left right, q), ts) <- triples
                , Just t <- Set.toList (unTerminalSet ts)
                ]
    resolveConflicts :: Either (String -> String) (Map.Map (ParserS, TSym) Action)
    resolveConflicts = foldr loop (Right init) getLATable where
        init :: Map.Map (ParserS, TSym) Action
        init = Map.fromList
            [ ((q, t), Shift p)
            | ((q, TS t), p) <- Map.toList (getEdges getCannonical0)
            ]
        loop :: ((ParserS, TSym), ProductionRule) -> Either (String -> String) (Map.Map (ParserS, TSym) Action) -> Either (String -> String) (Map.Map (ParserS, TSym) Action)
        loop _ (Left str) = Left str
        loop ((q, t), production) (Right getActionT) = case (Map.lookup (q, t) getActionT, if fst production == start' then Accept else Reduce production) of
            (Nothing, ra) -> Right (Map.insert (q, t) ra getActionT)
            (Just Accept, ra) -> Right getActionT
            (Just (Shift p), ra) -> case (Map.lookup t terminals', Map.lookup production productions') of
                (Just (assoc, prec1), Just prec2)
                    | prec1 > prec2 -> Right getActionT
                    | prec1 < prec2 -> Right (Map.update (const (Just ra)) (q, t) getActionT)
                    | assoc == ALeft -> Right (Map.update (const (Just ra)) (q, t) getActionT)
                    | assoc == ARight -> Right getActionT
                _ -> Left $ strcat
                    [ strstr "cannot resolve conflict: {" . nl
                    , strstr "  (" . showsPrec 0 q . strstr ", " . makeOutput 0 (TS t) . strstr ") +-> " . makeOutput 0 (Shift p) . nl
                    , strstr "  (" . showsPrec 0 q . strstr ", " . makeOutput 0 (TS t) . strstr ") +-> " . makeOutput 0 (Reduce production) . nl
                    , strstr "}" . nl
                    , makeOutput 0 getCannonical0
                    ]
            (Just (Reduce production'), ra) -> case (Map.lookup production' productions', Map.lookup production productions') of
                (Just prec1, Just prec2)
                    | prec1 > prec2 -> Right getActionT
                    | prec1 < prec2 -> Right (Map.update (const (Just ra)) (q, t) getActionT)
                _ -> Left $ strcat
                    [ strstr "cannot resolve conflict: {" . nl
                    , strstr "  (" . showsPrec 0 q . strstr ", " . makeOutput 0 (TS t) . strstr ") +-> " . makeOutput 0 (Reduce production) . nl
                    , strstr "  (" . showsPrec 0 q . strstr ", " . makeOutput 0 (TS t) . strstr ") +-> " . makeOutput 0 (Reduce production') . nl
                    , strstr "}" . nl
                    , makeOutput 0 getCannonical0
                    ]
    makeLALR1 :: ExceptT String Identity LR1Parser
    makeLALR1 = case resolveConflicts of
        Left delta -> throwE (delta "")
        Right getActionT -> return $ LR1Parser
            { getInitialS = getRoot getCannonical0
            , getActionTable = getActionT
            , getReduceTable = Map.fromList
                [ ((q, nt), p)
                | ((q, NS nt), p) <- Map.toList (getEdges getCannonical0)
                ]
            }

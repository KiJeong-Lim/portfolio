module Aladdin.Front.Analyzer.Parser where

import Aladdin.Front.Analyzer.Grammar
import Aladdin.Front.Header
import qualified Control.Monad.Trans.Class as Y
import qualified Control.Monad.Trans.Except as Y
import qualified Control.Monad.Trans.State.Strict as Y
import qualified Data.Map.Strict as YMap
import qualified Data.Set as YSet

type ParserS = Int

type NSym = Int

type TSym = Int

data Sym
    = NS NSym
    | TS TSym
    deriving (Eq, Ord)

data Action
    = Shift ParserS
    | Reduce (NSym, [Sym])
    | Accept
    deriving (Eq)

data LR1Parser
    = LR1Parser
        { getInitialS :: ParserS
        , getActionTable :: YMap.Map (ParserS, TSym) Action
        , getReduceTable :: YMap.Map (ParserS, NSym) ParserS
        }
    deriving ()

data ParsingTree
    = PTLeaf (Token)
    | PTBranch NSym [ParsingTree]
    deriving ()



runAladdinParser :: [Token] -> Either (Maybe (Token)) (Either TermRep [DeclRep])
runAladdinParser = fmap (getEither getQuery (getSequence getDecl)) . runLR1 theLR1Parser where
    getQuery :: ParsingTree -> (TermRep)
    getQuery (PTBranch _ [PTLeaf (T_quest loc_1), _2@(PTBranch guard2 _), PTLeaf (T_dot loc_3)])
        | [guard2] `elem` [[3]] =
            (getTermRep0 _2)
    getDecl :: ParsingTree -> (DeclRep)
    getDecl (PTBranch _ [PTLeaf (T_kind loc_1), PTLeaf (T_smallid loc_2 contents_2), _3@(PTBranch guard3 _), PTLeaf (T_dot loc_4)])
        | [guard3] `elem` [[14]] =
            RKindDecl ((loc_1) <> (loc_4)) (TC_Named (contents_2)) (getKindRep0 _3)
    getDecl (PTBranch _ [PTLeaf (T_type loc_1), PTLeaf (T_smallid loc_2 contents_2), _3@(PTBranch guard3 _), PTLeaf (T_dot loc_4)])
        | [guard3] `elem` [[16]] =
            RTypeDecl ((loc_1) <> (loc_4)) (DC_Named (contents_2)) (getTypeRep0 _3)
    getDecl (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (T_dot loc_2)])
        | [guard1] `elem` [[3]] =
            RFactDecl (getSLoc (getTermRep0 _1) <> (loc_2)) (getTermRep0 _1)
    getKindRep0 :: ParsingTree -> (KindRep)
    getKindRep0 (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (T_arrow loc_2), _3@(PTBranch guard3 _)])
        | [guard1, guard3] `elem` [[15, 14]] =
            RKArr (getSLoc (getKindRep1 _1) <> getSLoc (getKindRep0 _3)) (getKindRep1 _1) (getKindRep0 _3)
    getKindRep0 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[15]] =
            (getKindRep1 _1)
    getKindRep1 :: ParsingTree -> (KindRep)
    getKindRep1 (PTBranch _ [PTLeaf (T_type loc_1)])
        | otherwise =
            RStar (loc_1)
    getKindRep1 (PTBranch _ [PTLeaf (T_lparen loc_1), _2@(PTBranch guard2 _), PTLeaf (T_rparen loc_3)])
        | [guard2] `elem` [[14]] =
            RKPrn ((loc_1) <> (loc_3)) (getKindRep0 _2)
    getTypeRep0 :: ParsingTree -> (TypeRep)
    getTypeRep0 (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (T_arrow loc_2), _3@(PTBranch guard3 _)])
        | [guard1, guard3] `elem` [[17, 16]] =
            RTyApp (getSLoc (getTypeRep1 _1) <> getSLoc (getTypeRep0 _3)) (RTyApp (getSLoc (getTypeRep1 _1) <> (loc_2)) (RTyCon (loc_2) TC_Arrow) (getTypeRep1 _1)) (getTypeRep0 _3)
    getTypeRep0 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[17]] =
            (getTypeRep1 _1)
    getTypeRep1 :: ParsingTree -> (TypeRep)
    getTypeRep1 (PTBranch _ [_1@(PTBranch guard1 _), _2@(PTBranch guard2 _)])
        | [guard1, guard2] `elem` [[17, 18]] =
            RTyApp (getSLoc (getTypeRep1 _1) <> getSLoc (getTypeRep2 _2)) (getTypeRep1 _1) (getTypeRep2 _2)
    getTypeRep1 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[18]] =
            (getTypeRep2 _1)
    getTypeRep2 :: ParsingTree -> (TypeRep)
    getTypeRep2 (PTBranch _ [PTLeaf (T_largeid loc_1 contents_1)])
        | otherwise =
            RTyVar (loc_1) (contents_1)
    getTypeRep2 (PTBranch _ [PTLeaf (T_smallid loc_1 contents_1)])
        | otherwise =
            RTyCon (loc_1) (TC_Named (contents_1))
    getTypeRep2 (PTBranch _ [PTLeaf (T_lparen loc_1), _2@(PTBranch guard2 _), PTLeaf (T_rparen loc_3)])
        | [guard2] `elem` [[16]] =
            RTyPrn ((loc_1) <> (loc_3)) (getTypeRep0 _2)
    getTermRep0 :: ParsingTree -> (TermRep)
    getTermRep0 (PTBranch _ [PTLeaf (T_largeid loc_1 contents_1), PTLeaf (T_bslash loc_2), _3@(PTBranch guard3 _)])
        | [guard3] `elem` [[3]] =
            RAbs ((loc_1) <> getSLoc (getTermRep0 _3)) (contents_1) (getTermRep0 _3)
    getTermRep0 (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (T_if loc_2), _3@(PTBranch guard3 _)])
        | [guard1, guard3] `elem` [[4, 3]] =
            RApp (getSLoc (getTermRep1 _1) <> getSLoc (getTermRep0 _3)) (RApp (getSLoc (getTermRep1 _1) <> (loc_2)) (RCon (loc_2) (DC_LO LO_if)) (getTermRep1 _1)) (getTermRep0 _3)
    getTermRep0 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[4]] =
            (getTermRep1 _1)
    getTermRep1 :: ParsingTree -> (TermRep)
    getTermRep1 (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (T_semicolon loc_2), _3@(PTBranch guard3 _)])
        | [guard1, guard3] `elem` [[4, 5]] =
            RApp (getSLoc (getTermRep1 _1) <> getSLoc (getTermRep2 _3)) (RApp (getSLoc (getTermRep1 _1) <> (loc_2)) (RCon (loc_2) (DC_LO LO_or)) (getTermRep1 _1)) (getTermRep2 _3)
    getTermRep1 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[5]] =
            (getTermRep2 _1)
    getTermRep2 :: ParsingTree -> (TermRep)
    getTermRep2 (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (T_fatarrow loc_2), _3@(PTBranch guard3 _)])
        | [guard1, guard3] `elem` [[6, 5]] =
            RApp (getSLoc (getTermRep3 _1) <> getSLoc (getTermRep2 _3)) (RApp (getSLoc (getTermRep3 _1) <> (loc_2)) (RCon (loc_2) (DC_LO LO_imply)) (getTermRep3 _1)) (getTermRep2 _3)
    getTermRep2 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[6]] =
            (getTermRep3 _1)
    getTermRep3 :: ParsingTree -> (TermRep)
    getTermRep3 (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (T_comma loc_2), _3@(PTBranch guard3 _)])
        | [guard1, guard3] `elem` [[6, 7]] =
            RApp (getSLoc (getTermRep3 _1) <> getSLoc (getTermRep4 _3)) (RApp (getSLoc (getTermRep3 _1) <> (loc_2)) (RCon (loc_2) (DC_LO LO_and)) (getTermRep3 _1)) (getTermRep4 _3)
    getTermRep3 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[7]] =
            (getTermRep4 _1)
    getTermRep4 :: ParsingTree -> (TermRep)
    getTermRep4 (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (T_cons loc_2), _3@(PTBranch guard3 _)])
        | [guard1, guard3] `elem` [[8, 7]] =
            RApp (getSLoc (getTermRep5 _1) <> getSLoc (getTermRep4 _3)) (RApp (getSLoc (getTermRep5 _1) <> (loc_2)) (RCon (loc_2) DC_Cons) (getTermRep5 _1)) (getTermRep4 _3)
    getTermRep4 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[8]] =
            (getTermRep5 _1)
    getTermRep5 :: ParsingTree -> (TermRep)
    getTermRep5 (PTBranch _ [PTLeaf (T_pi loc_1), _2@(PTBranch guard2 _)])
        | [guard2] `elem` [[8]] =
            RApp ((loc_1) <> getSLoc (getTermRep5 _2)) (RCon (loc_1) (DC_LO LO_pi)) (getTermRep5 _2)
    getTermRep5 (PTBranch _ [PTLeaf (T_sigma loc_1), _2@(PTBranch guard2 _)])
        | [guard2] `elem` [[8]] =
            RApp ((loc_1) <> getSLoc (getTermRep5 _2)) (RCon (loc_1) (DC_LO LO_sigma)) (getTermRep5 _2)
    getTermRep5 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[9]] =
            (getTermRep6 _1)
    getTermRep6 :: ParsingTree -> (TermRep)
    getTermRep6 (PTBranch _ [_1@(PTBranch guard1 _), _2@(PTBranch guard2 _)])
        | [guard1, guard2] `elem` [[9, 10]] =
            RApp (getSLoc (getTermRep6 _1) <> getSLoc (getTermRep7 _2)) (getTermRep6 _1) (getTermRep7 _2)
    getTermRep6 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[10]] =
            (getTermRep7 _1)
    getTermRep6 (PTBranch _ [PTLeaf (T_succ loc_1)])
        | otherwise =
            RCon (loc_1) DC_Succ
    getTermRep7 :: ParsingTree -> (TermRep)
    getTermRep7 (PTBranch _ [PTLeaf (T_lparen loc_1), _2@(PTBranch guard2 _), PTLeaf (T_rparen loc_3)])
        | [guard2] `elem` [[3]] =
            RPrn ((loc_1) <> (loc_3)) (getTermRep0 _2)
    getTermRep7 (PTBranch _ [PTLeaf (T_cut loc_1)])
        | otherwise =
            RCon (loc_1) (DC_LO LO_cut)
    getTermRep7 (PTBranch _ [PTLeaf (T_true loc_1)])
        | otherwise =
            RCon (loc_1) (DC_LO LO_true)
    getTermRep7 (PTBranch _ [PTLeaf (T_fail loc_1)])
        | otherwise =
            RCon (loc_1) (DC_LO LO_fail)
    getTermRep7 (PTBranch _ [PTLeaf (T_smallid loc_1 contents_1)])
        | otherwise =
            RCon (loc_1) (DC_Named (contents_1))
    getTermRep7 (PTBranch _ [PTLeaf (T_largeid loc_1 contents_1)])
        | otherwise =
            RVar (loc_1) (contents_1)
    getTermRep7 (PTBranch _ [PTLeaf (T_nat_lit loc_1 contents_1)])
        | otherwise =
            mkNatLit (loc_1) (contents_1)
    getTermRep7 (PTBranch _ [PTLeaf (T_str_lit loc_1 contents_1)])
        | otherwise =
            mkStrLit (loc_1) (contents_1)
    getTermRep7 (PTBranch _ [PTLeaf (T_chr_lit loc_1 contents_1)])
        | otherwise =
            mkChrLit (loc_1) (contents_1)
    getTermRep7 (PTBranch _ [PTLeaf (T_lbracket loc_1), PTLeaf (T_rbracket loc_2)])
        | otherwise =
            RCon ((loc_1) <> (loc_2)) DC_Nil
    getTermRep7 (PTBranch _ [PTLeaf (T_lbracket loc_1), _2@(PTBranch guard2 _), PTLeaf (T_rbracket loc_3)])
        | [guard2] `elem` [[11]] =
            RPrn ((loc_1) <> (loc_3)) (getListBody _2)
    getSequence :: (ParsingTree -> (a)) -> ParsingTree -> ([a])
    getSequence getElem (PTBranch _ [])
        | otherwise =
            []
    getSequence getElem (PTBranch _ [_1@(PTBranch guard1 _), _2@(PTBranch guard2 _)])
        | [guard1, guard2] `elem` [[13, 12]] =
            (getElem _1) : (getSequence getElem _2)
    getEither :: (ParsingTree -> (a)) -> (ParsingTree -> (b)) -> ParsingTree -> (Either a b)
    getEither getLeft getRight (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[2]] =
            Left (getLeft _1)
    getEither getLeft getRight (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[12]] =
            Right (getRight _1)
    getListBody :: ParsingTree -> (TermRep)
    getListBody (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[8]] =
            RApp (getSLoc (getTermRep5 _1)) (RApp (getSLoc (getTermRep5 _1)) (RCon (getSLoc (getTermRep5 _1)) DC_Cons) (getTermRep5 _1)) (RCon (getSLoc (getTermRep5 _1)) DC_Nil)
    getListBody (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (T_comma loc_2), _3@(PTBranch guard3 _)])
        | [guard1, guard3] `elem` [[8, 11]] =
            RApp (getSLoc (getTermRep5 _1) <> getSLoc (getListBody _3)) (RApp (getSLoc (getTermRep5 _1) <> (loc_2)) (RCon (loc_2) DC_Cons) (getTermRep5 _1)) (getListBody _3)
    toTerminal :: (Token) -> TSym
    toTerminal (T_dot loc) = 1
    toTerminal (T_arrow loc) = 2
    toTerminal (T_lparen loc) = 3
    toTerminal (T_rparen loc) = 4
    toTerminal (T_lbracket loc) = 5
    toTerminal (T_rbracket loc) = 6
    toTerminal (T_quest loc) = 7
    toTerminal (T_if loc) = 8
    toTerminal (T_comma loc) = 9
    toTerminal (T_semicolon loc) = 10
    toTerminal (T_fatarrow loc) = 11
    toTerminal (T_pi loc) = 12
    toTerminal (T_sigma loc) = 13
    toTerminal (T_succ loc) = 14
    toTerminal (T_cut loc) = 15
    toTerminal (T_true loc) = 16
    toTerminal (T_fail loc) = 17
    toTerminal (T_bslash loc) = 18
    toTerminal (T_cons loc) = 19
    toTerminal (T_kind loc) = 20
    toTerminal (T_type loc) = 21
    toTerminal (T_smallid loc contents) = 22
    toTerminal (T_largeid loc contents) = 23
    toTerminal (T_nat_lit loc contents) = 24
    toTerminal (T_chr_lit loc contents) = 25
    toTerminal (T_str_lit loc contents) = 26
    runLR1 :: LR1Parser -> [Token] -> Either (Maybe (Token)) ParsingTree
    runLR1 (LR1Parser getInitS getActionT getReduceT) = go where
        loop inputs = do
            let cur = if null inputs then 0 else toTerminal (head inputs)
                exception = Y.lift (if null inputs then Left Nothing else Left (Just (head inputs)))
            (stack, trees) <- Y.get
            case YMap.lookup (head stack, cur) getActionT of
                Nothing -> exception
                Just Accept -> return ()
                Just (Shift top') -> do
                    Y.put (top' : stack, PTLeaf (head inputs) : trees)
                    loop (tail inputs)
                Just (Reduce (lhs, rhs)) -> do
                    let n = length rhs
                    case YMap.lookup (stack !! n, lhs) getReduceT of
                        Nothing -> exception
                        Just top' -> do
                            Y.put (top' : drop n stack, PTBranch lhs (reverse (take n trees)) : drop n trees)
                            loop inputs
        go tokens = do
            (_, (_, result)) <- Y.runStateT (loop tokens) ([getInitS], [])
            case result of
                [output] -> return output
    theLR1Parser :: LR1Parser
    theLR1Parser = LR1Parser
        { getInitialS = 0
        , getActionTable = YMap.fromAscList 
            [ ((0, 0), Reduce (12, [])), ((0, 3), Shift 19), ((0, 5), Shift 18), ((0, 7), Shift 22), ((0, 12), Shift 21), ((0, 13), Shift 23), ((0, 14), Shift 26), ((0, 15), Shift 14), ((0, 16), Shift 27), ((0, 17), Shift 15), ((0, 20), Shift 16), ((0, 21), Shift 28), ((0, 22), Shift 24), ((0, 23), Shift 17), ((0, 24), Shift 20), ((0, 25), Shift 13), ((0, 26), Shift 25)
            , ((1, 0), Reduce (12, [])), ((1, 3), Shift 19), ((1, 5), Shift 18), ((1, 12), Shift 21), ((1, 13), Shift 23), ((1, 14), Shift 26), ((1, 15), Shift 14), ((1, 16), Shift 27), ((1, 17), Shift 15), ((1, 20), Shift 16), ((1, 21), Shift 28), ((1, 22), Shift 24), ((1, 23), Shift 17), ((1, 24), Shift 20), ((1, 25), Shift 13), ((1, 26), Shift 25)
            , ((2, 0), Reduce (1, [NS 2]))
            , ((3, 1), Shift 30)
            , ((4, 1), Reduce (3, [NS 4])), ((4, 4), Reduce (3, [NS 4])), ((4, 8), Shift 39), ((4, 10), Shift 40)
            , ((5, 1), Reduce (4, [NS 5])), ((5, 4), Reduce (4, [NS 5])), ((5, 8), Reduce (4, [NS 5])), ((5, 10), Reduce (4, [NS 5]))
            , ((6, 1), Reduce (5, [NS 6])), ((6, 4), Reduce (5, [NS 6])), ((6, 8), Reduce (5, [NS 6])), ((6, 9), Shift 42), ((6, 10), Reduce (5, [NS 6])), ((6, 11), Shift 43)
            , ((7, 1), Reduce (6, [NS 7])), ((7, 4), Reduce (6, [NS 7])), ((7, 8), Reduce (6, [NS 7])), ((7, 9), Reduce (6, [NS 7])), ((7, 10), Reduce (6, [NS 7])), ((7, 11), Reduce (6, [NS 7]))
            , ((8, 1), Reduce (7, [NS 8])), ((8, 4), Reduce (7, [NS 8])), ((8, 8), Reduce (7, [NS 8])), ((8, 9), Reduce (7, [NS 8])), ((8, 10), Reduce (7, [NS 8])), ((8, 11), Reduce (7, [NS 8])), ((8, 19), Shift 44)
            , ((9, 1), Reduce (8, [NS 9])), ((9, 3), Shift 19), ((9, 4), Reduce (8, [NS 9])), ((9, 5), Shift 18), ((9, 6), Reduce (8, [NS 9])), ((9, 8), Reduce (8, [NS 9])), ((9, 9), Reduce (8, [NS 9])), ((9, 10), Reduce (8, [NS 9])), ((9, 11), Reduce (8, [NS 9])), ((9, 15), Shift 14), ((9, 16), Shift 27), ((9, 17), Shift 15), ((9, 19), Reduce (8, [NS 9])), ((9, 22), Shift 24), ((9, 23), Shift 35), ((9, 24), Shift 20), ((9, 25), Shift 13), ((9, 26), Shift 25)
            , ((10, 1), Reduce (9, [NS 10])), ((10, 3), Reduce (9, [NS 10])), ((10, 4), Reduce (9, [NS 10])), ((10, 5), Reduce (9, [NS 10])), ((10, 6), Reduce (9, [NS 10])), ((10, 8), Reduce (9, [NS 10])), ((10, 9), Reduce (9, [NS 10])), ((10, 10), Reduce (9, [NS 10])), ((10, 11), Reduce (9, [NS 10])), ((10, 15), Reduce (9, [NS 10])), ((10, 16), Reduce (9, [NS 10])), ((10, 17), Reduce (9, [NS 10])), ((10, 19), Reduce (9, [NS 10])), ((10, 22), Reduce (9, [NS 10])), ((10, 23), Reduce (9, [NS 10])), ((10, 24), Reduce (9, [NS 10])), ((10, 25), Reduce (9, [NS 10])), ((10, 26), Reduce (9, [NS 10]))
            , ((11, 0), Reduce (1, [NS 12]))
            , ((12, 0), Accept)
            , ((13, 1), Reduce (10, [TS 25])), ((13, 3), Reduce (10, [TS 25])), ((13, 4), Reduce (10, [TS 25])), ((13, 5), Reduce (10, [TS 25])), ((13, 6), Reduce (10, [TS 25])), ((13, 8), Reduce (10, [TS 25])), ((13, 9), Reduce (10, [TS 25])), ((13, 10), Reduce (10, [TS 25])), ((13, 11), Reduce (10, [TS 25])), ((13, 15), Reduce (10, [TS 25])), ((13, 16), Reduce (10, [TS 25])), ((13, 17), Reduce (10, [TS 25])), ((13, 19), Reduce (10, [TS 25])), ((13, 22), Reduce (10, [TS 25])), ((13, 23), Reduce (10, [TS 25])), ((13, 24), Reduce (10, [TS 25])), ((13, 25), Reduce (10, [TS 25])), ((13, 26), Reduce (10, [TS 25]))
            , ((14, 1), Reduce (10, [TS 15])), ((14, 3), Reduce (10, [TS 15])), ((14, 4), Reduce (10, [TS 15])), ((14, 5), Reduce (10, [TS 15])), ((14, 6), Reduce (10, [TS 15])), ((14, 8), Reduce (10, [TS 15])), ((14, 9), Reduce (10, [TS 15])), ((14, 10), Reduce (10, [TS 15])), ((14, 11), Reduce (10, [TS 15])), ((14, 15), Reduce (10, [TS 15])), ((14, 16), Reduce (10, [TS 15])), ((14, 17), Reduce (10, [TS 15])), ((14, 19), Reduce (10, [TS 15])), ((14, 22), Reduce (10, [TS 15])), ((14, 23), Reduce (10, [TS 15])), ((14, 24), Reduce (10, [TS 15])), ((14, 25), Reduce (10, [TS 15])), ((14, 26), Reduce (10, [TS 15]))
            , ((15, 1), Reduce (10, [TS 17])), ((15, 3), Reduce (10, [TS 17])), ((15, 4), Reduce (10, [TS 17])), ((15, 5), Reduce (10, [TS 17])), ((15, 6), Reduce (10, [TS 17])), ((15, 8), Reduce (10, [TS 17])), ((15, 9), Reduce (10, [TS 17])), ((15, 10), Reduce (10, [TS 17])), ((15, 11), Reduce (10, [TS 17])), ((15, 15), Reduce (10, [TS 17])), ((15, 16), Reduce (10, [TS 17])), ((15, 17), Reduce (10, [TS 17])), ((15, 19), Reduce (10, [TS 17])), ((15, 22), Reduce (10, [TS 17])), ((15, 23), Reduce (10, [TS 17])), ((15, 24), Reduce (10, [TS 17])), ((15, 25), Reduce (10, [TS 17])), ((15, 26), Reduce (10, [TS 17]))
            , ((16, 22), Shift 31)
            , ((17, 1), Reduce (10, [TS 23])), ((17, 3), Reduce (10, [TS 23])), ((17, 4), Reduce (10, [TS 23])), ((17, 5), Reduce (10, [TS 23])), ((17, 8), Reduce (10, [TS 23])), ((17, 9), Reduce (10, [TS 23])), ((17, 10), Reduce (10, [TS 23])), ((17, 11), Reduce (10, [TS 23])), ((17, 15), Reduce (10, [TS 23])), ((17, 16), Reduce (10, [TS 23])), ((17, 17), Reduce (10, [TS 23])), ((17, 18), Shift 41), ((17, 19), Reduce (10, [TS 23])), ((17, 22), Reduce (10, [TS 23])), ((17, 23), Reduce (10, [TS 23])), ((17, 24), Reduce (10, [TS 23])), ((17, 25), Reduce (10, [TS 23])), ((17, 26), Reduce (10, [TS 23]))
            , ((18, 3), Shift 19), ((18, 5), Shift 18), ((18, 6), Shift 36), ((18, 12), Shift 21), ((18, 13), Shift 23), ((18, 14), Shift 26), ((18, 15), Shift 14), ((18, 16), Shift 27), ((18, 17), Shift 15), ((18, 22), Shift 24), ((18, 23), Shift 35), ((18, 24), Shift 20), ((18, 25), Shift 13), ((18, 26), Shift 25)
            , ((19, 3), Shift 19), ((19, 5), Shift 18), ((19, 12), Shift 21), ((19, 13), Shift 23), ((19, 14), Shift 26), ((19, 15), Shift 14), ((19, 16), Shift 27), ((19, 17), Shift 15), ((19, 22), Shift 24), ((19, 23), Shift 17), ((19, 24), Shift 20), ((19, 25), Shift 13), ((19, 26), Shift 25)
            , ((20, 1), Reduce (10, [TS 24])), ((20, 3), Reduce (10, [TS 24])), ((20, 4), Reduce (10, [TS 24])), ((20, 5), Reduce (10, [TS 24])), ((20, 6), Reduce (10, [TS 24])), ((20, 8), Reduce (10, [TS 24])), ((20, 9), Reduce (10, [TS 24])), ((20, 10), Reduce (10, [TS 24])), ((20, 11), Reduce (10, [TS 24])), ((20, 15), Reduce (10, [TS 24])), ((20, 16), Reduce (10, [TS 24])), ((20, 17), Reduce (10, [TS 24])), ((20, 19), Reduce (10, [TS 24])), ((20, 22), Reduce (10, [TS 24])), ((20, 23), Reduce (10, [TS 24])), ((20, 24), Reduce (10, [TS 24])), ((20, 25), Reduce (10, [TS 24])), ((20, 26), Reduce (10, [TS 24]))
            , ((21, 3), Shift 19), ((21, 5), Shift 18), ((21, 12), Shift 21), ((21, 13), Shift 23), ((21, 14), Shift 26), ((21, 15), Shift 14), ((21, 16), Shift 27), ((21, 17), Shift 15), ((21, 22), Shift 24), ((21, 23), Shift 35), ((21, 24), Shift 20), ((21, 25), Shift 13), ((21, 26), Shift 25)
            , ((22, 3), Shift 19), ((22, 5), Shift 18), ((22, 12), Shift 21), ((22, 13), Shift 23), ((22, 14), Shift 26), ((22, 15), Shift 14), ((22, 16), Shift 27), ((22, 17), Shift 15), ((22, 22), Shift 24), ((22, 23), Shift 17), ((22, 24), Shift 20), ((22, 25), Shift 13), ((22, 26), Shift 25)
            , ((23, 3), Shift 19), ((23, 5), Shift 18), ((23, 12), Shift 21), ((23, 13), Shift 23), ((23, 14), Shift 26), ((23, 15), Shift 14), ((23, 16), Shift 27), ((23, 17), Shift 15), ((23, 22), Shift 24), ((23, 23), Shift 35), ((23, 24), Shift 20), ((23, 25), Shift 13), ((23, 26), Shift 25)
            , ((24, 1), Reduce (10, [TS 22])), ((24, 3), Reduce (10, [TS 22])), ((24, 4), Reduce (10, [TS 22])), ((24, 5), Reduce (10, [TS 22])), ((24, 6), Reduce (10, [TS 22])), ((24, 8), Reduce (10, [TS 22])), ((24, 9), Reduce (10, [TS 22])), ((24, 10), Reduce (10, [TS 22])), ((24, 11), Reduce (10, [TS 22])), ((24, 15), Reduce (10, [TS 22])), ((24, 16), Reduce (10, [TS 22])), ((24, 17), Reduce (10, [TS 22])), ((24, 19), Reduce (10, [TS 22])), ((24, 22), Reduce (10, [TS 22])), ((24, 23), Reduce (10, [TS 22])), ((24, 24), Reduce (10, [TS 22])), ((24, 25), Reduce (10, [TS 22])), ((24, 26), Reduce (10, [TS 22]))
            , ((25, 1), Reduce (10, [TS 26])), ((25, 3), Reduce (10, [TS 26])), ((25, 4), Reduce (10, [TS 26])), ((25, 5), Reduce (10, [TS 26])), ((25, 6), Reduce (10, [TS 26])), ((25, 8), Reduce (10, [TS 26])), ((25, 9), Reduce (10, [TS 26])), ((25, 10), Reduce (10, [TS 26])), ((25, 11), Reduce (10, [TS 26])), ((25, 15), Reduce (10, [TS 26])), ((25, 16), Reduce (10, [TS 26])), ((25, 17), Reduce (10, [TS 26])), ((25, 19), Reduce (10, [TS 26])), ((25, 22), Reduce (10, [TS 26])), ((25, 23), Reduce (10, [TS 26])), ((25, 24), Reduce (10, [TS 26])), ((25, 25), Reduce (10, [TS 26])), ((25, 26), Reduce (10, [TS 26]))
            , ((26, 1), Reduce (9, [TS 14])), ((26, 3), Reduce (9, [TS 14])), ((26, 4), Reduce (9, [TS 14])), ((26, 5), Reduce (9, [TS 14])), ((26, 6), Reduce (9, [TS 14])), ((26, 8), Reduce (9, [TS 14])), ((26, 9), Reduce (9, [TS 14])), ((26, 10), Reduce (9, [TS 14])), ((26, 11), Reduce (9, [TS 14])), ((26, 15), Reduce (9, [TS 14])), ((26, 16), Reduce (9, [TS 14])), ((26, 17), Reduce (9, [TS 14])), ((26, 19), Reduce (9, [TS 14])), ((26, 22), Reduce (9, [TS 14])), ((26, 23), Reduce (9, [TS 14])), ((26, 24), Reduce (9, [TS 14])), ((26, 25), Reduce (9, [TS 14])), ((26, 26), Reduce (9, [TS 14]))
            , ((27, 1), Reduce (10, [TS 16])), ((27, 3), Reduce (10, [TS 16])), ((27, 4), Reduce (10, [TS 16])), ((27, 5), Reduce (10, [TS 16])), ((27, 6), Reduce (10, [TS 16])), ((27, 8), Reduce (10, [TS 16])), ((27, 9), Reduce (10, [TS 16])), ((27, 10), Reduce (10, [TS 16])), ((27, 11), Reduce (10, [TS 16])), ((27, 15), Reduce (10, [TS 16])), ((27, 16), Reduce (10, [TS 16])), ((27, 17), Reduce (10, [TS 16])), ((27, 19), Reduce (10, [TS 16])), ((27, 22), Reduce (10, [TS 16])), ((27, 23), Reduce (10, [TS 16])), ((27, 24), Reduce (10, [TS 16])), ((27, 25), Reduce (10, [TS 16])), ((27, 26), Reduce (10, [TS 16]))
            , ((28, 22), Shift 32)
            , ((29, 0), Reduce (12, [NS 13, NS 12]))
            , ((30, 0), Reduce (13, [NS 3, TS 1])), ((30, 3), Reduce (13, [NS 3, TS 1])), ((30, 5), Reduce (13, [NS 3, TS 1])), ((30, 12), Reduce (13, [NS 3, TS 1])), ((30, 13), Reduce (13, [NS 3, TS 1])), ((30, 14), Reduce (13, [NS 3, TS 1])), ((30, 15), Reduce (13, [NS 3, TS 1])), ((30, 16), Reduce (13, [NS 3, TS 1])), ((30, 17), Reduce (13, [NS 3, TS 1])), ((30, 20), Reduce (13, [NS 3, TS 1])), ((30, 21), Reduce (13, [NS 3, TS 1])), ((30, 22), Reduce (13, [NS 3, TS 1])), ((30, 23), Reduce (13, [NS 3, TS 1])), ((30, 24), Reduce (13, [NS 3, TS 1])), ((30, 25), Reduce (13, [NS 3, TS 1])), ((30, 26), Reduce (13, [NS 3, TS 1]))
            , ((31, 3), Shift 50), ((31, 21), Shift 51)
            , ((32, 3), Shift 56), ((32, 22), Shift 57), ((32, 23), Shift 55)
            , ((33, 6), Shift 66)
            , ((34, 6), Reduce (11, [NS 8])), ((34, 9), Shift 58)
            , ((35, 1), Reduce (10, [TS 23])), ((35, 3), Reduce (10, [TS 23])), ((35, 4), Reduce (10, [TS 23])), ((35, 5), Reduce (10, [TS 23])), ((35, 6), Reduce (10, [TS 23])), ((35, 8), Reduce (10, [TS 23])), ((35, 9), Reduce (10, [TS 23])), ((35, 10), Reduce (10, [TS 23])), ((35, 11), Reduce (10, [TS 23])), ((35, 15), Reduce (10, [TS 23])), ((35, 16), Reduce (10, [TS 23])), ((35, 17), Reduce (10, [TS 23])), ((35, 19), Reduce (10, [TS 23])), ((35, 22), Reduce (10, [TS 23])), ((35, 23), Reduce (10, [TS 23])), ((35, 24), Reduce (10, [TS 23])), ((35, 25), Reduce (10, [TS 23])), ((35, 26), Reduce (10, [TS 23]))
            , ((36, 1), Reduce (10, [TS 5, TS 6])), ((36, 3), Reduce (10, [TS 5, TS 6])), ((36, 4), Reduce (10, [TS 5, TS 6])), ((36, 5), Reduce (10, [TS 5, TS 6])), ((36, 6), Reduce (10, [TS 5, TS 6])), ((36, 8), Reduce (10, [TS 5, TS 6])), ((36, 9), Reduce (10, [TS 5, TS 6])), ((36, 10), Reduce (10, [TS 5, TS 6])), ((36, 11), Reduce (10, [TS 5, TS 6])), ((36, 15), Reduce (10, [TS 5, TS 6])), ((36, 16), Reduce (10, [TS 5, TS 6])), ((36, 17), Reduce (10, [TS 5, TS 6])), ((36, 19), Reduce (10, [TS 5, TS 6])), ((36, 22), Reduce (10, [TS 5, TS 6])), ((36, 23), Reduce (10, [TS 5, TS 6])), ((36, 24), Reduce (10, [TS 5, TS 6])), ((36, 25), Reduce (10, [TS 5, TS 6])), ((36, 26), Reduce (10, [TS 5, TS 6]))
            , ((37, 1), Shift 59)
            , ((38, 4), Shift 67)
            , ((39, 3), Shift 19), ((39, 5), Shift 18), ((39, 12), Shift 21), ((39, 13), Shift 23), ((39, 14), Shift 26), ((39, 15), Shift 14), ((39, 16), Shift 27), ((39, 17), Shift 15), ((39, 22), Shift 24), ((39, 23), Shift 17), ((39, 24), Shift 20), ((39, 25), Shift 13), ((39, 26), Shift 25)
            , ((40, 3), Shift 19), ((40, 5), Shift 18), ((40, 12), Shift 21), ((40, 13), Shift 23), ((40, 14), Shift 26), ((40, 15), Shift 14), ((40, 16), Shift 27), ((40, 17), Shift 15), ((40, 22), Shift 24), ((40, 23), Shift 35), ((40, 24), Shift 20), ((40, 25), Shift 13), ((40, 26), Shift 25)
            , ((41, 3), Shift 19), ((41, 5), Shift 18), ((41, 12), Shift 21), ((41, 13), Shift 23), ((41, 14), Shift 26), ((41, 15), Shift 14), ((41, 16), Shift 27), ((41, 17), Shift 15), ((41, 22), Shift 24), ((41, 23), Shift 17), ((41, 24), Shift 20), ((41, 25), Shift 13), ((41, 26), Shift 25)
            , ((42, 3), Shift 19), ((42, 5), Shift 18), ((42, 12), Shift 21), ((42, 13), Shift 23), ((42, 14), Shift 26), ((42, 15), Shift 14), ((42, 16), Shift 27), ((42, 17), Shift 15), ((42, 22), Shift 24), ((42, 23), Shift 35), ((42, 24), Shift 20), ((42, 25), Shift 13), ((42, 26), Shift 25)
            , ((43, 3), Shift 19), ((43, 5), Shift 18), ((43, 12), Shift 21), ((43, 13), Shift 23), ((43, 14), Shift 26), ((43, 15), Shift 14), ((43, 16), Shift 27), ((43, 17), Shift 15), ((43, 22), Shift 24), ((43, 23), Shift 35), ((43, 24), Shift 20), ((43, 25), Shift 13), ((43, 26), Shift 25)
            , ((44, 3), Shift 19), ((44, 5), Shift 18), ((44, 12), Shift 21), ((44, 13), Shift 23), ((44, 14), Shift 26), ((44, 15), Shift 14), ((44, 16), Shift 27), ((44, 17), Shift 15), ((44, 22), Shift 24), ((44, 23), Shift 35), ((44, 24), Shift 20), ((44, 25), Shift 13), ((44, 26), Shift 25)
            , ((45, 1), Reduce (8, [TS 12, NS 8])), ((45, 4), Reduce (8, [TS 12, NS 8])), ((45, 6), Reduce (8, [TS 12, NS 8])), ((45, 8), Reduce (8, [TS 12, NS 8])), ((45, 9), Reduce (8, [TS 12, NS 8])), ((45, 10), Reduce (8, [TS 12, NS 8])), ((45, 11), Reduce (8, [TS 12, NS 8])), ((45, 19), Reduce (8, [TS 12, NS 8]))
            , ((46, 1), Reduce (8, [TS 13, NS 8])), ((46, 4), Reduce (8, [TS 13, NS 8])), ((46, 6), Reduce (8, [TS 13, NS 8])), ((46, 8), Reduce (8, [TS 13, NS 8])), ((46, 9), Reduce (8, [TS 13, NS 8])), ((46, 10), Reduce (8, [TS 13, NS 8])), ((46, 11), Reduce (8, [TS 13, NS 8])), ((46, 19), Reduce (8, [TS 13, NS 8]))
            , ((47, 1), Reduce (9, [NS 9, NS 10])), ((47, 3), Reduce (9, [NS 9, NS 10])), ((47, 4), Reduce (9, [NS 9, NS 10])), ((47, 5), Reduce (9, [NS 9, NS 10])), ((47, 6), Reduce (9, [NS 9, NS 10])), ((47, 8), Reduce (9, [NS 9, NS 10])), ((47, 9), Reduce (9, [NS 9, NS 10])), ((47, 10), Reduce (9, [NS 9, NS 10])), ((47, 11), Reduce (9, [NS 9, NS 10])), ((47, 15), Reduce (9, [NS 9, NS 10])), ((47, 16), Reduce (9, [NS 9, NS 10])), ((47, 17), Reduce (9, [NS 9, NS 10])), ((47, 19), Reduce (9, [NS 9, NS 10])), ((47, 22), Reduce (9, [NS 9, NS 10])), ((47, 23), Reduce (9, [NS 9, NS 10])), ((47, 24), Reduce (9, [NS 9, NS 10])), ((47, 25), Reduce (9, [NS 9, NS 10])), ((47, 26), Reduce (9, [NS 9, NS 10]))
            , ((48, 1), Shift 68)
            , ((49, 1), Reduce (14, [NS 15])), ((49, 2), Shift 71), ((49, 4), Reduce (14, [NS 15]))
            , ((50, 3), Shift 50), ((50, 21), Shift 51)
            , ((51, 1), Reduce (15, [TS 21])), ((51, 2), Reduce (15, [TS 21])), ((51, 4), Reduce (15, [TS 21]))
            , ((52, 1), Shift 69)
            , ((53, 1), Reduce (16, [NS 17])), ((53, 2), Shift 75), ((53, 3), Shift 56), ((53, 4), Reduce (16, [NS 17])), ((53, 22), Shift 57), ((53, 23), Shift 55)
            , ((54, 1), Reduce (17, [NS 18])), ((54, 2), Reduce (17, [NS 18])), ((54, 3), Reduce (17, [NS 18])), ((54, 4), Reduce (17, [NS 18])), ((54, 22), Reduce (17, [NS 18])), ((54, 23), Reduce (17, [NS 18]))
            , ((55, 1), Reduce (18, [TS 23])), ((55, 2), Reduce (18, [TS 23])), ((55, 3), Reduce (18, [TS 23])), ((55, 4), Reduce (18, [TS 23])), ((55, 22), Reduce (18, [TS 23])), ((55, 23), Reduce (18, [TS 23]))
            , ((56, 3), Shift 56), ((56, 22), Shift 57), ((56, 23), Shift 55)
            , ((57, 1), Reduce (18, [TS 22])), ((57, 2), Reduce (18, [TS 22])), ((57, 3), Reduce (18, [TS 22])), ((57, 4), Reduce (18, [TS 22])), ((57, 22), Reduce (18, [TS 22])), ((57, 23), Reduce (18, [TS 22]))
            , ((58, 3), Shift 19), ((58, 5), Shift 18), ((58, 12), Shift 21), ((58, 13), Shift 23), ((58, 14), Shift 26), ((58, 15), Shift 14), ((58, 16), Shift 27), ((58, 17), Shift 15), ((58, 22), Shift 24), ((58, 23), Shift 35), ((58, 24), Shift 20), ((58, 25), Shift 13), ((58, 26), Shift 25)
            , ((59, 0), Reduce (2, [TS 7, NS 3, TS 1]))
            , ((60, 1), Reduce (3, [NS 4, TS 8, NS 3])), ((60, 4), Reduce (3, [NS 4, TS 8, NS 3]))
            , ((61, 1), Reduce (3, [TS 23, TS 18, NS 3])), ((61, 4), Reduce (3, [TS 23, TS 18, NS 3]))
            , ((62, 1), Reduce (4, [NS 4, TS 10, NS 5])), ((62, 4), Reduce (4, [NS 4, TS 10, NS 5])), ((62, 8), Reduce (4, [NS 4, TS 10, NS 5])), ((62, 10), Reduce (4, [NS 4, TS 10, NS 5]))
            , ((63, 1), Reduce (5, [NS 6, TS 11, NS 5])), ((63, 4), Reduce (5, [NS 6, TS 11, NS 5])), ((63, 8), Reduce (5, [NS 6, TS 11, NS 5])), ((63, 10), Reduce (5, [NS 6, TS 11, NS 5]))
            , ((64, 1), Reduce (6, [NS 6, TS 9, NS 7])), ((64, 4), Reduce (6, [NS 6, TS 9, NS 7])), ((64, 8), Reduce (6, [NS 6, TS 9, NS 7])), ((64, 9), Reduce (6, [NS 6, TS 9, NS 7])), ((64, 10), Reduce (6, [NS 6, TS 9, NS 7])), ((64, 11), Reduce (6, [NS 6, TS 9, NS 7]))
            , ((65, 1), Reduce (7, [NS 8, TS 19, NS 7])), ((65, 4), Reduce (7, [NS 8, TS 19, NS 7])), ((65, 8), Reduce (7, [NS 8, TS 19, NS 7])), ((65, 9), Reduce (7, [NS 8, TS 19, NS 7])), ((65, 10), Reduce (7, [NS 8, TS 19, NS 7])), ((65, 11), Reduce (7, [NS 8, TS 19, NS 7]))
            , ((66, 1), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 3), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 4), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 5), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 6), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 8), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 9), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 10), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 11), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 15), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 16), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 17), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 19), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 22), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 23), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 24), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 25), Reduce (10, [TS 5, NS 11, TS 6])), ((66, 26), Reduce (10, [TS 5, NS 11, TS 6]))
            , ((67, 1), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 3), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 4), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 5), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 6), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 8), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 9), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 10), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 11), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 15), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 16), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 17), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 19), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 22), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 23), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 24), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 25), Reduce (10, [TS 3, NS 3, TS 4])), ((67, 26), Reduce (10, [TS 3, NS 3, TS 4]))
            , ((68, 0), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 3), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 5), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 12), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 13), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 14), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 15), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 16), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 17), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 20), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 21), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 22), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 23), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 24), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 25), Reduce (13, [TS 20, TS 22, NS 14, TS 1])), ((68, 26), Reduce (13, [TS 20, TS 22, NS 14, TS 1]))
            , ((69, 0), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 3), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 5), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 12), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 13), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 14), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 15), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 16), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 17), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 20), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 21), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 22), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 23), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 24), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 25), Reduce (13, [TS 21, TS 22, NS 16, TS 1])), ((69, 26), Reduce (13, [TS 21, TS 22, NS 16, TS 1]))
            , ((70, 4), Shift 77)
            , ((71, 3), Shift 50), ((71, 21), Shift 51)
            , ((72, 6), Reduce (11, [NS 8, TS 9, NS 11]))
            , ((73, 4), Shift 79)
            , ((74, 1), Reduce (17, [NS 17, NS 18])), ((74, 2), Reduce (17, [NS 17, NS 18])), ((74, 3), Reduce (17, [NS 17, NS 18])), ((74, 4), Reduce (17, [NS 17, NS 18])), ((74, 22), Reduce (17, [NS 17, NS 18])), ((74, 23), Reduce (17, [NS 17, NS 18]))
            , ((75, 3), Shift 56), ((75, 22), Shift 57), ((75, 23), Shift 55)
            , ((76, 1), Reduce (14, [NS 15, TS 2, NS 14])), ((76, 4), Reduce (14, [NS 15, TS 2, NS 14]))
            , ((77, 1), Reduce (15, [TS 3, NS 14, TS 4])), ((77, 2), Reduce (15, [TS 3, NS 14, TS 4])), ((77, 4), Reduce (15, [TS 3, NS 14, TS 4]))
            , ((78, 1), Reduce (16, [NS 17, TS 2, NS 16])), ((78, 4), Reduce (16, [NS 17, TS 2, NS 16]))
            , ((79, 1), Reduce (18, [TS 3, NS 16, TS 4])), ((79, 2), Reduce (18, [TS 3, NS 16, TS 4])), ((79, 3), Reduce (18, [TS 3, NS 16, TS 4])), ((79, 4), Reduce (18, [TS 3, NS 16, TS 4])), ((79, 22), Reduce (18, [TS 3, NS 16, TS 4])), ((79, 23), Reduce (18, [TS 3, NS 16, TS 4]))
            ]
        , getReduceTable = YMap.fromAscList 
            [ ((0, 1), 12), ((0, 2), 2), ((0, 3), 3), ((0, 4), 4), ((0, 5), 5), ((0, 6), 6), ((0, 7), 7), ((0, 8), 8), ((0, 9), 9), ((0, 10), 10), ((0, 12), 11), ((0, 13), 1)
            , ((1, 3), 3), ((1, 4), 4), ((1, 5), 5), ((1, 6), 6), ((1, 7), 7), ((1, 8), 8), ((1, 9), 9), ((1, 10), 10), ((1, 12), 29), ((1, 13), 1)
            , ((9, 10), 47)
            , ((18, 8), 34), ((18, 9), 9), ((18, 10), 10), ((18, 11), 33)
            , ((19, 3), 38), ((19, 4), 4), ((19, 5), 5), ((19, 6), 6), ((19, 7), 7), ((19, 8), 8), ((19, 9), 9), ((19, 10), 10)
            , ((21, 8), 45), ((21, 9), 9), ((21, 10), 10)
            , ((22, 3), 37), ((22, 4), 4), ((22, 5), 5), ((22, 6), 6), ((22, 7), 7), ((22, 8), 8), ((22, 9), 9), ((22, 10), 10)
            , ((23, 8), 46), ((23, 9), 9), ((23, 10), 10)
            , ((31, 14), 48), ((31, 15), 49)
            , ((32, 16), 52), ((32, 17), 53), ((32, 18), 54)
            , ((39, 3), 60), ((39, 4), 4), ((39, 5), 5), ((39, 6), 6), ((39, 7), 7), ((39, 8), 8), ((39, 9), 9), ((39, 10), 10)
            , ((40, 5), 62), ((40, 6), 6), ((40, 7), 7), ((40, 8), 8), ((40, 9), 9), ((40, 10), 10)
            , ((41, 3), 61), ((41, 4), 4), ((41, 5), 5), ((41, 6), 6), ((41, 7), 7), ((41, 8), 8), ((41, 9), 9), ((41, 10), 10)
            , ((42, 7), 64), ((42, 8), 8), ((42, 9), 9), ((42, 10), 10)
            , ((43, 5), 63), ((43, 6), 6), ((43, 7), 7), ((43, 8), 8), ((43, 9), 9), ((43, 10), 10)
            , ((44, 7), 65), ((44, 8), 8), ((44, 9), 9), ((44, 10), 10)
            , ((50, 14), 70), ((50, 15), 49)
            , ((53, 18), 74)
            , ((56, 16), 73), ((56, 17), 53), ((56, 18), 54)
            , ((58, 8), 34), ((58, 9), 9), ((58, 10), 10), ((58, 11), 72)
            , ((71, 14), 76), ((71, 15), 49)
            , ((75, 16), 78), ((75, 17), 53), ((75, 18), 54)
            ]
        }


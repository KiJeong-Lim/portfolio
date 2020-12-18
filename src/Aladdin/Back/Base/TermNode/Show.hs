module Aladdin.Back.Base.TermNode.Show where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Identifier
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import Data.Unique
import qualified Data.Map.Strict as Map
import Lib.Base

data TermViewer
    = IVarViewer Int
    | LVarViewer String
    | TVarViewer String
    | IAbsViewer Int TermViewer
    | IAppViewer TermViewer TermViewer
    | ChrLViewer Char
    | StrLViewer String
    | NatLViewer Integer
    | ListViewer [TermViewer]
    | DConViewer Identifier [TermViewer]
    | TConViewer Identifier [TermViewer]
    | TAppViewer TermViewer TermViewer
    deriving ()

instance Show TermViewer where
    showList viewers = strstr "[" . ppunc ", " (map (showsPrec 6) viewers) . strstr "]"
    showsPrec prec = go where
        parenthesize :: Int -> (String -> String) -> String -> String
        parenthesize prec' delta
            | prec > prec' = strstr "(" . delta . strstr ")"
            | otherwise = delta
        go :: TermViewer -> String -> String
        go (IVarViewer var) = parenthesize 10 (strstr "W_" . showsPrec 0 var)
        go (LVarViewer var) = parenthesize 10 (strstr var)
        go (TVarViewer var) = parenthesize 10 (strstr var)
        go (IAbsViewer var viewer1) = parenthesize 0 (strstr "W_" . showsPrec 0 var . strstr "\\ " . showsPrec 0 viewer1)
        go (IAppViewer viewer1 viewer2) = parenthesize 9 (showsPrec 9 viewer1 . strstr " " . showsPrec 10 viewer2)
        go (ChrLViewer chr) = parenthesize 10 (showsPrec 0 chr)
        go (StrLViewer str) = parenthesize 10 (showsPrec 0 str)
        go (NatLViewer nat) = parenthesize 10 (showsPrec 0 nat)
        go (ListViewer viewers) = showList viewers
        go (DConViewer iden viewers) = case iden of
            ID_InfixOperator associativity precedence str
                | [viewer1, viewer2] <- viewers -> case associativity of
                    A_left -> parenthesize precedence (showsPrec precedence viewer1 . strstr str . showsPrec (precedence + 1) viewer2)
                    A_right -> parenthesize precedence (showsPrec (precedence + 1) viewer1 . strstr str . showsPrec precedence viewer2)
                    A_none -> parenthesize precedence (showsPrec (precedence + 1) viewer1 . strstr str . showsPrec (precedence + 1) viewer2)
            ID_PrefixOperator precedence str
                | [viewer1] <- viewers -> parenthesize precedence (showsPrec precedence viewer1)
            ID_Name str
                | [] <- viewers -> parenthesize 10 (strstr str)

instance Show TermNode where
    showList = ppunc "\n" . map (showsPrec 0)
    showsPrec prec = showsPrec prec . makeTermViewer

viewRep :: Show a => Identifier -> a -> Bool
viewRep iden x = maybe False (\iden' -> iden == iden') (Map.lookup (show x) theReservedSymbols)

theReservedSymbols :: Map.Map String Identifier
theReservedSymbols = Map.fromList
    [ (show LO_ty_pi, ID_PrefixOperator 0 "Lambda ")
    , (show LO_if, ID_InfixOperator A_right 0 " :- ")
    , (show LO_true, ID_Name "true")
    , (show LO_fail, ID_Name "fail")
    , (show LO_cut, ID_Name "!")
    , (show LO_imply, ID_InfixOperator A_right 2 " => ")
    , (show LO_pi, ID_PrefixOperator 5 "pi ")
    , (show LO_sigma, ID_PrefixOperator 5 "sigma ")
    , (show DC_cons, ID_InfixOperator A_right 6 " :: ")
    , (show DC_succ, ID_PrefixOperator 9 "++")
    , (show DC_nil, ID_Name "[]")
    , (show DC_eq, ID_InfixOperator A_none 5 " = ")
    , (show TC_arrow, ID_InfixOperator A_right 5 " -> ")
    , (show TC_o, ID_Name "o")
    , (show TC_list, ID_Name "list")
    , (show TC_char, ID_Name "char")
    ]

makeTermViewer :: TermNode -> TermViewer
makeTermViewer = fst . runIdentity . uncurry (runStateT . format . erase) . runIdentity . flip runStateT 1 . build [] . rewrite NF where
    isType :: TermViewer -> IsTypeLevel
    isType (TVarViewer _) = True
    isType (TConViewer _ _) = True
    isType (TAppViewer _ _) = True
    isType _ = False
    buildCon :: Constant -> TermViewer
    buildCon (DC data_constructor)
        = case data_constructor of
            DC_Named iden -> DConViewer iden []
            DC_ChrL chr -> ChrLViewer chr
            DC_NatL nat -> NatLViewer nat
            DC_Unique uni -> DConViewer (ID_Name (show (hashUnique uni))) []
            other -> case Map.lookup (show other) theReservedSymbols of
                Nothing -> DConViewer (ID_Name (show other)) []
                Just iden -> DConViewer iden []
    buildCon (TC type_constructor)
        = case type_constructor of
            TC_Named iden -> TConViewer iden []
            TC_Unique uni -> TConViewer (ID_Name (show (hashUnique uni))) []
            other -> case Map.lookup (show other) theReservedSymbols of
                Nothing -> TConViewer (ID_Name (show other)) []
                Just iden -> TConViewer iden []
    buildCon (LO logical_operator)
        = case Map.lookup (show logical_operator) theReservedSymbols of
            Nothing -> DConViewer (ID_Name (show logical_operator)) []
            Just iden -> DConViewer iden []
    build :: [Int] -> TermNode -> StateT Int Identity TermViewer
    build vars (LVar v)
        = case v of
            LV_ty_var uni -> return (TVarViewer ("TVar_" ++ show (hashUnique uni)))
            LV_Unique uni -> return (LVarViewer ("LVar_" ++ show (hashUnique uni)))
            LV_Named str -> return (LVarViewer str)
    build vars (NCon c)
        = return (buildCon c)
    build vars (NIdx i)
        = return (IVarViewer (vars !! (i - 1)))
    build vars (NApp t1 t2)
        = do
            t1_rep <- build vars t1
            t2_rep <- build vars t2
            if isType t1_rep
                then return (TAppViewer t1_rep t2_rep)
                else return (IAppViewer t1_rep t2_rep)
    build vars (NAbs t)
        = do
            v <- get
            put (v + 1)
            t_rep <- build (v : vars) t
            return (IAbsViewer v t_rep)
    erase :: TermViewer -> TermViewer
    erase (TAppViewer (DConViewer __nil _) (TConViewer __char _))
        | viewRep __nil DC_nil && viewRep __char TC_char
        = StrLViewer ""
    erase (TConViewer con viewers)
        = TConViewer con viewers
    erase (TAppViewer viewer1 viewer2)
        = TAppViewer (erase viewer1) (erase viewer2)
    erase (IVarViewer var)
        = IVarViewer var
    erase (LVarViewer var)
        = LVarViewer var
    erase (IAbsViewer var viewer)
        = IAbsViewer var (erase viewer)
    erase (IAppViewer viewer1 viewer2)
        = IAppViewer (erase viewer1) (erase viewer2)
    erase (ChrLViewer chr)
        = ChrLViewer chr
    erase (DConViewer c viewers)    
        = DConViewer c (map erase viewers)
    format :: TermViewer -> StateT Int Identity TermViewer
    format (DConViewer __nil _)
        | viewRep __nil DC_nil
        = return (ListViewer [])
    format (IAppViewer (IAppViewer (DConViewer __cons _) (ChrLViewer chr)) viewer2)
        | viewRep __cons DC_cons
        = do
            viewer2' <- format viewer2
            case viewer2' of
                StrLViewer str -> return (StrLViewer (chr : str))
                _ -> return (DConViewer __cons [ChrLViewer chr, viewer2'])
    format (IAppViewer (IAppViewer (DConViewer __cons _) viewer1) viewer2)
        | viewRep __cons DC_cons
        = do
            viewer1' <- format viewer1
            viewer2' <- format viewer2
            case viewer2' of
                ListViewer viewers' -> return (ListViewer (viewer1' : viewers'))
                _ -> return (DConViewer __cons [viewer1', viewer2'])
    format (IAppViewer (IAppViewer (DConViewer infix_op _) viewer1) viewer2)
        | isInfixOp infix_op
        = do
            viewer1' <- format viewer1
            viewer2' <- format viewer2
            return (DConViewer infix_op [viewer1', viewer2'])
    format (IAppViewer (DConViewer infix_op _) viewer1)
        | isInfixOp infix_op
        = do
            viewer1' <- format viewer1
            v <- get
            put (v + 1)
            return (IAbsViewer v (DConViewer infix_op [IVarViewer v, viewer1']))
    format (DConViewer infix_op _)
        | isInfixOp infix_op
        = do
            v <- get
            put (v + 2)
            return (IAbsViewer v (IAbsViewer (v + 1) (DConViewer infix_op [IVarViewer v, IVarViewer (v + 1)])))
    format (IAppViewer (DConViewer prefix_op _) viewer1)
        | isPrefixOp prefix_op
        = do
            viewer1' <- format viewer1
            return (DConViewer prefix_op [viewer1'])
    format (DConViewer prefix_op _)
        | isPrefixOp prefix_op
        = do
            v <- get
            put (v + 1)
            return (IAbsViewer v (DConViewer prefix_op [IVarViewer v]))
    format (DConViewer name _)
        = return (DConViewer name [])
    format (IAppViewer (TAppViewer (TConViewer infix_op _) viewer1) viewer2)
        | isInfixOp infix_op
        = do
            viewer1' <- format viewer1
            viewer2' <- format viewer2
            return (TConViewer infix_op [viewer1', viewer2'])
    format (TAppViewer (TConViewer prefix_op _) viewer1)
        | isPrefixOp prefix_op
        = do
            viewer1' <- format viewer1
            return (TConViewer prefix_op [viewer1'])
    format (TConViewer name _)
        = return (TConViewer name [])
    format (IVarViewer var)
        = return (IVarViewer var)
    format (LVarViewer var)
        = return (LVarViewer var)
    format (TVarViewer var)
        = return (TVarViewer var)
    format (IAbsViewer var viewer1)
        = do
            viewer1' <- format viewer1
            return (IAbsViewer var viewer1')
    format (IAppViewer viewer1 viewer2)
        = do
            viewer1' <- format viewer1
            viewer2' <- format viewer2
            return (IAppViewer viewer1' viewer2')
    format (ChrLViewer chr)
        = return (ChrLViewer chr)

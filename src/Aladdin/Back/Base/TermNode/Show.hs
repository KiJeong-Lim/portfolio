module Aladdin.Back.Base.TermNode.Show where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Front.Header
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

data Fixity extra
    = Prefix String extra
    | Suffix extra String
    | InfixL extra String extra
    | InfixR extra String extra
    | InfixN extra String extra
    deriving ()

data ViewNode
    = ViewIVar Int
    | ViewLVar LargeId
    | ViewDCon SmallId
    | ViewIApp ViewNode ViewNode
    | ViewIAbs Int ViewNode
    | ViewTVar LargeId
    | ViewTCon SmallId
    | ViewTApp ViewNode ViewNode
    | ViewOper (Fixity ViewNode, Precedence)
    | ViewNatL Integer
    | ViewChrL Char
    | ViewStrL String
    | ViewList [ViewNode]
    deriving ()

instance Show TermNode where
    showsPrec prec = pprint prec . constructViewer

instance Outputable ViewNode where
    pprint prec = go where
        parenthesize :: Precedence -> (String -> String) -> String -> String
        parenthesize prec' delta
            | prec > prec' = strstr "(" . delta . strstr ")"
            | otherwise = delta
        go :: ViewNode -> String -> String
        go (ViewIVar var) = strstr "W_" . showsPrec 0 var
        go (ViewLVar var) = strstr var
        go (ViewDCon con) = strstr con
        go (ViewIApp viewer1 viewer2) = parenthesize 6 (pprint 6 viewer1 . strstr " " . pprint 7 viewer2)
        go (ViewIAbs var viewer1) = parenthesize 0 (strstr "W_" . showsPrec 0 var . strstr "\\ " . pprint 0 viewer1)
        go (ViewTVar var) = strstr var
        go (ViewTCon con) = strstr con
        go (ViewTApp viewer1 viewer2) = parenthesize 6 (pprint 6 viewer1 . strstr " " . pprint 7 viewer2)
        go (ViewOper (oper, prec')) = case oper of
            Prefix str viewer1 -> parenthesize prec' (strstr str . pprint prec' viewer1)
            Suffix viewer1 str -> parenthesize prec' (pprint prec' viewer1 . strstr str)
            InfixL viewer1 str viewer2 -> parenthesize prec' (pprint prec' viewer1 . strstr str . pprint (prec' + 1) viewer2)
            InfixR viewer1 str viewer2 -> parenthesize prec' (pprint (prec' + 1) viewer1 . strstr str . pprint prec' viewer2)
            InfixN viewer1 str viewer2 -> parenthesize prec' (pprint (prec' + 1) viewer1 . strstr str . pprint (prec' + 1) viewer2)
        go (ViewChrL chr) = showsPrec 0 chr
        go (ViewStrL str) = showsPrec 0 str
        go (ViewNatL nat) = showsPrec 0 nat
        go (ViewList viewers) = strstr "[" . ppunc ", " (map (pprint 5) viewers) . strstr "]"

constructViewer :: TermNode -> ViewNode
constructViewer = fst . runIdentity . uncurry (runStateT . formatView . eraseType) . runIdentity . flip runStateT 1 . makeView [] . rewrite NF where
    isType :: ViewNode -> Bool
    isType (ViewTVar _) = True
    isType (ViewTCon _) = True
    isType (ViewTApp _ _) = True
    isType _ = False
    makeView :: [Int] -> TermNode -> StateT Int Identity ViewNode
    makeView vars (LVar var) = case var of
        LV_ty_var v -> return (ViewTVar ("TV_" ++ show v))
        LV_Unique v -> return (ViewLVar ("V_" ++ show v))
        LV_Named v -> return (ViewLVar v)
    makeView vars (NCon con) = case con of
        DC data_constructor -> case data_constructor of
            DC_LO logical_operator -> case logical_operator of
                LO_ty_pi -> return (ViewDCon "Lambda")
                LO_if -> return (ViewDCon ":-")
                LO_true -> return (ViewDCon "true")
                LO_fail -> return (ViewDCon "fail")
                LO_cut -> return (ViewDCon "!")
                LO_and -> return (ViewDCon ",")
                LO_or -> return (ViewDCon ";")
                LO_imply -> return (ViewDCon "=>")
                LO_pi -> return (ViewDCon "pi")
                LO_sigma -> return (ViewDCon "sigma")
            DC_Named name -> return (ViewDCon ("__" ++ name))
            DC_Unique uni -> return (ViewDCon ("c_" ++ show uni))
            DC_Nil -> return (ViewDCon "[]")
            DC_Cons -> return (ViewDCon "::")
            DC_ChrL chr -> return (ViewChrL chr)
            DC_NatL nat -> return (ViewNatL nat)
            DC_Succ -> return (ViewDCon "__s")
            DC_Eq -> return (ViewDCon "=")
        TC type_constructor -> case type_constructor of
            TC_Arrow -> return (ViewTCon "->")
            TC_Unique uni -> return (ViewTCon ("tc_" ++ show uni))
            TC_Named name -> return (ViewTCon ("__" ++ name))
    makeView vars (NIdx idx) = return (ViewIVar (vars !! (idx - 1)))
    makeView vars (NApp t1 t2) = do
        t1_rep <- makeView vars t1
        t2_rep <- makeView vars t2
        return (if isType t1_rep then ViewTApp t1_rep t2_rep else ViewIApp t1_rep t2_rep)
    makeView vars (NAbs t) = do
        var <- get
        let var' = var + 1
        put var'
        t_rep <- makeView (var : vars) t
        return (ViewIAbs var t_rep)
    eraseType :: ViewNode -> ViewNode
    eraseType (ViewIApp (ViewDCon "[]") (ViewTCon "__char")) = ViewStrL ""
    eraseType (ViewTCon c) = ViewTCon c
    eraseType (ViewTApp t1 t2) = ViewTApp (eraseType t1) (eraseType t2)
    eraseType (ViewIVar v) = ViewIVar v
    eraseType (ViewLVar v) = ViewLVar v
    eraseType (ViewTVar v) = ViewTVar v
    eraseType (ViewIAbs v t) = ViewIAbs v (eraseType t)
    eraseType (ViewIApp t1 t2) = if isType t2 then eraseType t1 else ViewIApp (eraseType t1) (eraseType t2)
    eraseType (ViewNatL nat) = ViewNatL nat
    eraseType (ViewChrL chr) = ViewChrL chr
    eraseType (ViewDCon c) = ViewDCon c
    checkOper :: String -> Maybe (Fixity (), Precedence)
    checkOper "->" = Just (InfixR () " -> " (), 4)
    checkOper "::" = Just (InfixR () " :: " (), 4)
    checkOper "Lambda" = Just (Prefix "Lambda " (), 0)
    checkOper ":-" = Just (InfixR () " :- " (), 0)
    checkOper ";" = Just (InfixL () "; " (), 1)
    checkOper "," = Just (InfixL () ", " (), 3)
    checkOper "=>" = Just (InfixR () " => " (), 2)
    checkOper "pi" = Just (Prefix "pi " (), 5)
    checkOper "sigma" = Just (Prefix "sigma " (), 5)
    checkOper "=" = Just (InfixN () " = " (), 5)
    checkOper _ = Nothing
    formatView :: ViewNode -> StateT Int Identity ViewNode
    formatView (ViewDCon "[]") = return (ViewList [])
    formatView (ViewIApp (ViewIApp (ViewDCon "::") (ViewChrL chr)) t) = do
        t' <- formatView t
        case t' of
            ViewStrL str -> return (ViewStrL (chr : str))
            t' -> return (ViewOper (InfixR (ViewChrL chr) " :: " t', 4))
    formatView (ViewIApp (ViewIApp (ViewDCon "::") t1) t2) = do
        t1' <- formatView t1
        t2' <- formatView t2
        case t2' of
            ViewList ts -> return (ViewList (t1' : ts))
            _ -> return (ViewOper (InfixR t1' " :: " t2', 4))
    formatView (ViewIApp (ViewIApp (ViewDCon con) t1) t2)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                t1' <- formatView t1
                t2' <- formatView t2
                return (ViewIApp (ViewOper (Prefix str t1', prec)) t2')
            Suffix _ str -> do
                t1' <- formatView t1
                t2' <- formatView t2
                return (ViewIApp (ViewOper (Suffix t1' str, prec)) t2')
            InfixL _ str _ -> do
                t1' <- formatView t1
                t2' <- formatView t2
                return (ViewOper (InfixL t1' str t2', prec))
            InfixR _ str _ -> do
                t1' <- formatView t1
                t2' <- formatView t2
                return (ViewOper (InfixR t1' str t2', prec))
            InfixN _ str _ -> do
                t1' <- formatView t1
                t2' <- formatView t2
                return (ViewOper (InfixN t1' str t2', prec))
    formatView (ViewIApp (ViewDCon con) t1)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                t1' <- formatView t1
                return (ViewOper (Prefix str t1', prec))
            Suffix _ str -> do
                t1' <- formatView t1
                return (ViewOper (Suffix t1' str, prec))
            InfixL _ str _ -> do
                t1' <- formatView t1
                v2 <- get
                let v2' = v2 + 1
                v2' `seq` put v2'
                return (ViewIAbs v2 (ViewOper (InfixL t1' str (ViewIVar v2), prec)))
            InfixR _ str _ -> do
                t1' <- formatView t1
                v2 <- get
                let v2' = v2 + 1
                v2' `seq` put v2'
                return (ViewIAbs v2 (ViewOper (InfixR t1' str (ViewIVar v2), prec)))
            InfixN _ str _ -> do
                t1' <- formatView t1
                v2 <- get
                let v2' = v2 + 1
                v2' `seq` put v2'
                return (ViewIAbs v2 (ViewOper (InfixN t1' str (ViewIVar v2), prec)))
    formatView (ViewDCon con)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                v1 <- get
                put (v1 + 1)
                return (ViewIAbs v1 (ViewOper (Prefix str (ViewIVar v1), prec)))
            Suffix _ str -> do
                v1 <- get
                put (v1 + 1)
                return (ViewIAbs v1 (ViewOper (Suffix (ViewIVar v1) str, prec)))
            InfixL _ str _ -> do
                v1 <- get
                let v2 = v1 + 1
                put (v2 + 1)
                return (ViewIAbs v1 (ViewIAbs v2 (ViewOper (InfixL (ViewIVar v1) str (ViewIVar v2), prec))))
            InfixR _ str _ -> do
                v1 <- get
                let v2 = v1 + 1
                put (v2 + 1)
                return (ViewIAbs v1 (ViewIAbs v2 (ViewOper (InfixR (ViewIVar v1) str (ViewIVar v2), prec))))
            InfixN _ str _ -> do
                v1 <- get
                let v2 = v1 + 1
                put (v2 + 1)
                return (ViewIAbs v1 (ViewIAbs v2 (ViewIAbs v2 (ViewOper (InfixN (ViewIVar v1) str (ViewIVar v2), prec)))))
    formatView (ViewTApp (ViewTApp (ViewTCon "->") t1) t2) = do
        t1' <- formatView t1
        t2' <- formatView t2
        return (ViewOper (InfixR t1' " -> " t2', 4))
    formatView (ViewIApp t1 t2) = do
        t1' <- formatView t1
        t2' <- formatView t2
        return (ViewIApp t1' t2')
    formatView (ViewTApp t1 t2) = do
        t1' <- formatView t1
        t2' <- formatView t2
        return (ViewTApp t1' t2')
    formatView (ViewIAbs v1 t2) = do
        t2' <- formatView t2
        return (ViewIAbs v1 t2')
    formatView (ViewDCon ('_' : '_' : c)) = return (ViewDCon c)
    formatView (ViewTCon ('_' : '_' : c)) = return (ViewTCon c)
    formatView viewer = return viewer

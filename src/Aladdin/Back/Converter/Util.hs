module Aladdin.Back.Converter.Util where

import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Front.Header
import Aladdin.Front.TypeChecker.Util
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

viewIAbs :: TermExpr dcon annot -> ([IVar], TermExpr dcon annot)
viewIAbs = go [] where
    go :: [IVar] -> TermExpr dcon annot -> ([IVar], TermExpr dcon annot)
    go vars (IAbs annot var term) = go (var : vars) term
    go vars term = (vars, term)

unFoldIApp :: TermExpr dcon annot -> (TermExpr dcon annot, [TermExpr dcon annot])
unFoldIApp = flip go [] where
    go :: TermExpr dcon annot -> [TermExpr dcon annot] -> (TermExpr dcon annot, [TermExpr dcon annot])
    go (IApp annot term1 term2) terms = go term1 (term2 : terms)
    go term terms = (term, terms)

isPredicate :: MonoType Int -> Bool
isPredicate (TyCon (TCon (TC_Named "o") _)) = True
isPredicate (TyApp (TyApp (TyCon (TCon TC_Arrow _)) typ1) typ2) = isPredicate typ2
isPredicate _ = False

reduceTermExpr :: TermExpr dcon annot -> TermExpr dcon annot
reduceTermExpr = go Map.empty where
    go :: Map.Map IVar (TermExpr tapp annot) -> TermExpr tapp annot -> TermExpr tapp annot
    go mapsto (IApp annot1 (IAbs annot2 var term1) term2)
        = go mapsto (go (Map.singleton var term2) term1)
    go mapsto (IVar annot var)
        = case Map.lookup var mapsto of
            Nothing -> IVar annot var
            Just term -> term
    go mapsto (DCon annot con)
        = DCon annot con
    go mapsto (IApp annot term1 term2)
        = IApp annot (go mapsto term1) (go mapsto term2)
    go mapsto (IAbs annot var term)
        = IAbs annot var (go mapsto term)

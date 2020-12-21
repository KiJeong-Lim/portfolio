module Aladdin.Front.Desugarer.ForTerm where

import Aladdin.Front.Analyzer.Grammar
import Aladdin.Front.Header
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

desugarTerm :: GenUniqueM m => TermRep -> StateT (Map.Map LargeId IVar) m (TermExpr DataConstructor SLoc)
desugarTerm (RVar loc1 "_") = do
    var <- getNewUnique
    return (IVar loc1 var)
desugarTerm (RVar loc1 var_rep) = do
    env <- get
    case Map.lookup var_rep env of
        Nothing -> do
            var <- getNewUnique
            put (Map.insert var_rep var env)
            return (IVar loc1 var)
        Just var -> return (IVar loc1 var)
desugarTerm (RCon loc1 con) = return (DCon loc1 con)
desugarTerm (RApp loc1 term_rep_1 term_rep_2) = do
    term_1 <- desugarTerm term_rep_1
    term_2 <- desugarTerm term_rep_2
    return (IApp loc1 term_1 term_2)
desugarTerm (RAbs loc1 var_rep term_rep) = do
    var <- getNewUnique
    env <- get
    case Map.lookup var_rep env of
        Nothing -> do
            put (Map.insert var_rep var env)
            term <- desugarTerm term_rep
            modify (Map.delete var_rep)
            return (IAbs loc1 var term)
        Just var' -> do
            put (Map.insert var_rep var (Map.delete var_rep env))
            term <- desugarTerm term_rep
            modify (Map.insert var_rep var' . Map.delete var_rep)
            return (IAbs loc1 var term)
desugarTerm (RPrn loc1 term_rep) = desugarTerm term_rep

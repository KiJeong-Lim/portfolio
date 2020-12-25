module Butterfly.Back.Base.CoreTerm where

import Butterfly.Back.Base.Util
import Control.Monad
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

type GuaranteeIVarRenamed = ()

type FreeVars = Set.Set IVar

type FreeVarCandidate = IVar

type CoreAbsn var annot = ([var], CoreTerm var annot)

type CoreDefn var annot = (var, CoreAbsn var annot)

type Bindings var annot = (IsRec, [CoreDefn var annot])

type CoreAltn var annot = (Tag, CoreAbsn var annot)

type CoreTops var annot = [CoreDefn var annot]

data CoreTerm var annot
    = CT_Var annot var
    | CT_Con annot Tag
    | CT_App annot (CoreTerm var annot) (CoreTerm var annot)
    | CT_Let annot (Bindings var annot) (CoreTerm var annot)
    | CT_Mat annot (CoreTerm var annot) [CoreAltn var annot]
    | CT_Lam annot (CoreAbsn var annot)
    deriving (Eq, Show)

instance Functor (CoreTerm var) where
    fmap fun (CT_Var annot var) = CT_Var (fun annot) var
    fmap fun (CT_Con annot con) = CT_Con (fun annot) con
    fmap fun (CT_App annot term1 term2) = CT_App (fun annot) (fmap fun term1) (fmap fun term2)
    fmap fun (CT_Let annot (is_rec, defns) body) = CT_Let (fun annot) (is_rec, [ (var, (params, fmap fun rhs)) | (var, (params, rhs)) <- defns ]) (fmap fun body)
    fmap fun (CT_Mat annot body altns) = CT_Mat (fun annot) (fmap fun body) [ (tag, (params, fmap fun rhs)) | (tag, (params, rhs)) <- altns ]
    fmap fun (CT_Lam annot (params, body)) = CT_Lam (fun annot) (params, fmap fun body)

instance HasAnnot (CoreTerm var) where
    getAnnot (CT_Var annot var) = annot
    getAnnot (CT_Con annot con) = annot
    getAnnot (CT_App annot term1 term2) = annot
    getAnnot (CT_Let annot (is_rec, defns) body) = annot
    getAnnot (CT_Mat annot body altns) = annot
    getAnnot (CT_Lam annot (params, body)) = annot

getFVsOfTops :: CoreTops IVar GuaranteeIVarRenamed -> CoreTops IVar FreeVars
getFVsOfTops tops = [ (var, (params, runIdentity (getFVsOfTerm (Set.fromList params) rhs))) | (var, (params, rhs)) <- tops ] where
    getFVsOfTerm :: Set.Set FreeVarCandidate -> CoreTerm IVar GuaranteeIVarRenamed -> Identity (CoreTerm IVar FreeVars)
    getFVsOfTerm vars (CT_Var _ var)
        | var `Set.member` vars = return (CT_Var (Set.singleton var) var)
        | otherwise = return (CT_Var Set.empty var)
    getFVsOfTerm vars (CT_Con _ con) = return (CT_Con Set.empty con)
    getFVsOfTerm vars (CT_App _ term1 term2) = do
        term1' <- getFVsOfTerm vars term1
        term2' <- getFVsOfTerm vars term2
        return (CT_App (getAnnot term1' `Set.union` getAnnot term2') term1' term2')
    getFVsOfTerm vars (CT_Let _ (is_rec, defns) body) = do
        let body_vars = foldr Set.insert vars (map fst defns)
            rhs_vars = if is_rec then body_vars else vars
        defns' <- sequence
            [ do
                rhs' <- getFVsOfTerm (rhs_vars `Set.union` Set.fromList params) rhs
                return (var, (params, rhs'))
            | (var, (params, rhs)) <- defns
            ]
        body' <- getFVsOfTerm body_vars body
        if is_rec
            then return (CT_Let (foldr Set.union (foldr Set.delete (getAnnot body') (map fst defns)) [ foldr Set.delete (Set.delete var (getAnnot rhs')) params | (var, (params, rhs')) <- defns' ]) (is_rec, defns') body')
            else return (CT_Let (foldr Set.union (getAnnot body') [ foldr Set.delete (getAnnot rhs') params | (var, (params, rhs')) <- defns' ]) (is_rec, defns') body')
    getFVsOfTerm vars (CT_Mat _ body altns) = do
        body' <- getFVsOfTerm vars body
        altns' <- sequence
            [ do
                rhs' <- getFVsOfTerm (vars `Set.union` Set.fromList params) rhs
                return (tag, (params, rhs'))
            | (tag, (params, rhs)) <- altns
            ]
        return (CT_Mat (foldr Set.union (getAnnot body') [ foldr Set.delete (getAnnot rhs') params | (tag, (params, rhs')) <- altns' ]) body' altns')
    getFVsOfTerm vars (CT_Lam _ (params, body)) = do
        body' <- getFVsOfTerm (vars `Set.union` Set.fromList params) body
        return (CT_Lam (getAnnot body' `Set.difference` Set.fromList params) (params, body'))

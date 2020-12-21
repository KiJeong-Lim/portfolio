module Aladdin.Front.Analyzer.Grammar where

import Aladdin.Front.Header

data Token
    = T_dot SLoc
    | T_arrow SLoc
    | T_lparen SLoc
    | T_rparen SLoc
    | T_lbracket SLoc
    | T_rbracket SLoc
    | T_quest SLoc
    | T_if SLoc
    | T_comma SLoc
    | T_semicolon SLoc
    | T_fatarrow SLoc
    | T_succ SLoc
    | T_pi SLoc
    | T_sigma SLoc
    | T_cut SLoc
    | T_true SLoc
    | T_fail SLoc
    | T_bslash SLoc
    | T_cons SLoc
    | T_kind SLoc
    | T_type SLoc
    | T_smallid SLoc SmallId
    | T_largeid SLoc LargeId
    | T_nat_lit SLoc Integer
    | T_chr_lit SLoc Char
    | T_str_lit SLoc String
    deriving (Show)

data TermRep
    = RVar SLoc LargeId
    | RCon SLoc DataConstructor
    | RApp SLoc TermRep TermRep
    | RAbs SLoc LargeId TermRep
    | RPrn SLoc TermRep
    deriving (Show)

data TypeRep
    = RTyVar SLoc LargeId
    | RTyCon SLoc TypeConstructor
    | RTyApp SLoc TypeRep TypeRep
    | RTyPrn SLoc TypeRep
    deriving (Show)

data KindRep
    = RStar SLoc
    | RKArr SLoc KindRep KindRep
    | RKPrn SLoc KindRep
    deriving (Show)

data DeclRep
    = RKindDecl SLoc TypeConstructor KindRep
    | RTypeDecl SLoc DataConstructor TypeRep
    | RFactDecl SLoc TermRep
    deriving (Show)

instance HasSLoc Token where
    getSLoc token = case token of
        T_dot loc -> loc
        T_arrow loc -> loc
        T_lparen loc -> loc
        T_rparen loc -> loc
        T_lbracket loc -> loc
        T_rbracket loc -> loc
        T_if loc -> loc
        T_quest loc -> loc
        T_comma loc -> loc
        T_semicolon loc -> loc
        T_fatarrow loc -> loc
        T_succ loc -> loc
        T_pi loc -> loc
        T_sigma loc -> loc
        T_cut loc -> loc
        T_true loc -> loc
        T_fail loc -> loc
        T_bslash loc -> loc
        T_cons loc -> loc
        T_kind loc -> loc
        T_type loc -> loc
        T_smallid loc _ -> loc
        T_largeid loc _ -> loc
        T_nat_lit loc _ -> loc
        T_chr_lit loc _ -> loc
        T_str_lit loc _ -> loc

instance HasSLoc TermRep where
    getSLoc term_rep = case term_rep of
        RVar loc _ -> loc
        RCon loc _ -> loc
        RApp loc _ _ -> loc
        RAbs loc _ _ -> loc
        RPrn loc _ -> loc

instance HasSLoc TypeRep where
    getSLoc type_rep = case type_rep of
        RTyVar loc _ -> loc
        RTyCon loc _ -> loc
        RTyApp loc _ _ -> loc
        RTyPrn loc _ -> loc

instance HasSLoc KindRep where
    getSLoc kind_rep = case kind_rep of
        RStar loc -> loc
        RKArr loc _ _ -> loc
        RKPrn loc _ -> loc

mkNatLit :: SLoc -> Integer -> TermRep
mkNatLit loc nat = RCon loc (DC_NatL nat)

mkChrLit :: SLoc -> Char -> TermRep
mkChrLit loc chr = RCon loc (DC_ChrL chr)

mkStrLit :: SLoc -> String -> TermRep
mkStrLit loc str = foldr (\ch -> \acc -> RApp loc (RApp loc (RCon loc DC_Cons) (RCon loc (DC_ChrL ch))) acc) (RCon loc DC_Nil) str

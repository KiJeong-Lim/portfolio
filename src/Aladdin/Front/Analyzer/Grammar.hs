module Aladdin.Front.Analyzer.Grammar where

import Aladdin.Front.Header

data AladinToken
    = ATQuest SLoc
    | ATSemicolon SLoc
    | ATKind SLoc
    | ATType SLoc
    | ATArrow SLoc
    | ATStar SLoc
    | ATLParen SLoc
    | ATRParen SLoc
    | ATIf SLoc
    | ATBSlash SLoc
    | ATOr SLoc
    | ATImply SLoc
    | ATAnd SLoc
    | ATCut SLoc
    | ATLBracket SLoc
    | ATRBracket SLoc
    | ATCons SLoc
    | ATSmallId SLoc SmallId
    | ATLargeId SLoc LargeId
    | ATLiteral SLoc Literal
    deriving (Eq, Show)

data Decl
    = KindDecl SLoc SmallId KindRep
    | TypeDecl SLoc SmallId TypeRep
    | FactDecl SLoc TermRep
    deriving (Eq, Show)

data KindRep
    = RStar SLoc
    | RKArr SLoc KindRep KindRep
    | RKInd SLoc KindRep
    deriving (Eq, Show)

data TypeRep
    = RTyVar SLoc LargeId
    | RTyCon SLoc SmallId
    | RTyApp SLoc TypeRep TypeRep
    | RTyArr SLoc TypeRep TypeRep
    | RTyInd SLoc TypeRep
    deriving (Eq, Show)

data TermRep
    = RVar SLoc LargeId
    | RCon SLoc SmallId
    | RApp SLoc TermRep TermRep
    | RAbs SLoc LargeId TermRep
    | RInd SLoc TermRep
    deriving (Eq, Show)

instance HasSLoc AladinToken where
    getSLoc atoken = case atoken of
        ATQuest loc -> loc
        ATSemicolon loc -> loc
        ATKind loc -> loc
        ATType loc -> loc
        ATArrow loc -> loc
        ATStar loc -> loc
        ATLParen loc -> loc
        ATRParen loc -> loc
        ATIf loc -> loc
        ATBSlash loc -> loc
        ATOr loc -> loc
        ATImply loc -> loc
        ATAnd loc -> loc
        ATCut loc -> loc
        ATLBracket loc -> loc
        ATRBracket loc -> loc
        ATCons loc -> loc
        ATSmallId loc _ -> loc
        ATLargeId loc _ -> loc
        ATLiteral loc _ -> loc

instance HasSLoc Decl where
    getSLoc decl = case decl of
        KindDecl loc _ _ -> loc
        TypeDecl loc _ _ -> loc
        FactDecl loc _ -> loc

instance HasSLoc KindRep where
    getSLoc krep = case krep of
        RStar loc -> loc
        RKArr loc _ _ -> loc
        RKInd loc _ -> loc

instance HasSLoc TypeRep where
    getSLoc trep = case trep of
        RTyVar loc _ -> loc
        RTyCon loc _ -> loc
        RTyApp loc _ _ -> loc
        RTyArr loc _ _ -> loc
        RTyInd loc _ -> loc

instance HasSLoc TermRep where
    getSLoc rep = case rep of
        RVar loc _ -> loc
        RCon loc _ -> loc
        RApp loc _ _ -> loc
        RAbs loc _ _ -> loc
        RInd loc _ -> loc

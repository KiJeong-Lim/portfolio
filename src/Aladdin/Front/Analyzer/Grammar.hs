module Aladdin.Front.Analyzer.Grammar where

import Aladdin.Front.Header

data AladdinToken smallid
    = AT_nat_lit SLoc Integer
    | AT_str_lit SLoc String
    | AT_chr_lit SLoc Char
    | AT_keyword SLoc String
    | AT_largeid SLoc String
    | AT_smallid SLoc smallid
    deriving (Show)

instance HasSLoc (AladdinToken smallid) where
    getSLoc token = case token of
        AT_nat_lit loc _ -> loc
        AT_str_lit loc _ -> loc
        AT_chr_lit loc _ -> loc
        AT_keyword loc _ -> loc
        AT_largeid loc _ -> loc
        AT_smallid loc _ -> loc



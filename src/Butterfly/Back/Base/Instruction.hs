module Butterfly.Back.Base.Instruction where

import Butterfly.Back.Base.Util

type GmCode = [GmInstruction]

data GmInstruction
    = GI_slide Int
    | GI_alloc Int
    | GI_update Int
    | GI_pop Int
    | GI_mk_var Int
    | GI_mk_con Tag
    | GI_mk_fun AdrOfSC
    | GI_mk_app
    | GI_mk_lam
    | GI_eval
    | GI_jump [(Tag, GmCode)]
    | GT_print
    deriving (Show)

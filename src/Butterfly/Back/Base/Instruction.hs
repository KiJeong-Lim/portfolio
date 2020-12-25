module Butterfly.Back.Base.Instruction where

import Butterfly.Back.Base.Util

type GmCode = [GmInstruction]

data GmInstruction
    = GI_slide Int
    | GI_alloc Int
    | GI_update Int
    | GI_pop Int
    | GI_push_var Int
    | GI_push_con Tag
    | GI_push_fun Arity (AdrOf GmCode)
    | GI_mk_app
    | GI_mk_abs
    | GI_eval
    | GI_jump [(Tag, AdrOf GmCode)]
    | GT_print
    | GT_put_str String
    deriving (Show)

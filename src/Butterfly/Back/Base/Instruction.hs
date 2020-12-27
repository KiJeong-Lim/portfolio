module Butterfly.Back.Base.Instruction where

import Butterfly.Back.Base.Util

type GmCode = [GmInstruction]

data GmInstruction
    = GI_slide Int
    | GI_alloc Int
    | GI_update Int
    | GI_install_gbl
    | GI_pop Int
    | GI_push Int
    | GI_push_con Tag
    | GI_push_fun (FunAdr, Arity)
    | GI_push_gbl GlobalIdx
    | GI_mk_app
    | GI_mk_abs
    | GI_eval
    | GI_jump [((Tag, Arity), GmCode)]
    | GT_print
    | GT_put_str String
    deriving (Show)

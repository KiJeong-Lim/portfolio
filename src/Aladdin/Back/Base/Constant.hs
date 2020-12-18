module Aladdin.Back.Base.Constant where

import Aladdin.Back.Base.Identifier
import Data.Unique
import Lib.Base

data LogicalOperator
    = LO_ty_pi
    | LO_if
    | LO_true
    | LO_fail
    | LO_cut
    | LO_and
    | LO_or
    | LO_imply
    | LO_sigma
    | LO_pi
    deriving (Eq, Ord)

data DataConstructor
    = DC_Named Identifier
    | DC_Unique Unique
    | DC_ChrL Char
    | DC_NatL Integer
    | DC_succ
    | DC_nil
    | DC_cons
    | DC_eq
    deriving (Eq, Ord)

data TypeConstructor
    = TC_arrow
    | TC_o
    | TC_list
    | TC_char
    | TC_Named Identifier
    | TC_Unique Unique
    deriving (Eq, Ord)

data Constant
    = LO LogicalOperator
    | DC DataConstructor
    | TC TypeConstructor
    deriving (Eq, Ord)

class ToConstant a where
    makeConstant :: a -> Constant

instance Show LogicalOperator where
    showList = undefined
    showsPrec prec = strstr . go where
        go :: LogicalOperator -> String
        go LO_ty_pi = "__ty_pi"
        go LO_if = "__if"
        go LO_true = "__true"
        go LO_fail = "__fail"
        go LO_cut = "__cut"
        go LO_and = "__and"
        go LO_or = "__or"
        go LO_imply = "__imply"
        go LO_sigma = "__sigma"
        go LO_pi = "__pi"

instance Show DataConstructor where
    showList = undefined
    showsPrec prec (DC_Named iden) = showsPrec 0 iden
    showsPrec prec (DC_Unique uni) = strstr "dcon_" . showsPrec 0 (hashUnique uni)
    showsPrec prec (DC_ChrL chr) = showsPrec 0 chr
    showsPrec prec (DC_NatL nat) = showsPrec 0 nat
    showsPrec prec (DC_succ) = strstr "__succ"
    showsPrec prec (DC_nil) = strstr "__nil"
    showsPrec prec (DC_cons) = strstr "__cons"
    showsPrec prec (DC_eq) = strstr "__eq"

instance Show TypeConstructor where
    showList = undefined
    showsPrec prec (TC_arrow) = strstr "__arrow"
    showsPrec prec (TC_o) = strstr "__o"
    showsPrec prec (TC_list) = strstr "__list"
    showsPrec prec (TC_char) = strstr "__char"
    showsPrec prec (TC_Named iden) = showsPrec 0 iden
    showsPrec prec (TC_Unique uni) = strstr "tcon_" . showsPrec 0 (hashUnique uni)

instance Show Constant where
    showList = undefined
    showsPrec prec (LO logical_operator) = showsPrec prec logical_operator
    showsPrec prec (DC data_constructor) = showsPrec prec data_constructor
    showsPrec prec (TC type_constructor) = showsPrec prec type_constructor

instance ToConstant LogicalOperator where
    makeConstant logical_operator
        = logical_operator `seq` LO logical_operator

instance ToConstant DataConstructor where
    makeConstant (DC_NatL n)
        | n >= 0 = DC (DC_NatL n)
        | otherwise = error "`makeConstant\': negative integer"
    makeConstant data_constructor = data_constructor `seq` DC data_constructor

instance ToConstant TypeConstructor where
    makeConstant type_constructor = type_constructor `seq` TC type_constructor

instance ToConstant Constant where
    makeConstant = id

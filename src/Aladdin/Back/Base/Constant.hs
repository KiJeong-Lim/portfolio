module Aladdin.Back.Base.Constant where

import Aladdin.Front.Header
import Lib.Base

data Constant
    = DC DataConstructor
    | TC TypeConstructor
    deriving (Eq, Ord)

class ToConstant a where
    makeConstant :: a -> Constant

instance Show Constant where
    showsPrec prec (DC data_constructor) = showsPrec prec data_constructor
    showsPrec prec (TC type_constructor) = showsPrec prec type_constructor

instance ToConstant LogicalOperator where
    makeConstant logical_operator = logical_operator `seq` DC (DC_LO logical_operator)

instance ToConstant DataConstructor where
    makeConstant (DC_NatL n)
        | n >= 0 = DC (DC_NatL n)
        | otherwise = error "`makeConstant\': negative integer"
    makeConstant data_constructor = data_constructor `seq` DC data_constructor

instance ToConstant TypeConstructor where
    makeConstant type_constructor = type_constructor `seq` TC type_constructor

instance ToConstant Constant where
    makeConstant = id

module Aladdin.Back.Base.Identifier where

import Lib.Base

type Name = String

data Associativity
    = A_left
    | A_right
    | A_none
    deriving (Eq, Ord)

data Identifier
    = ID_InfixOperator Associativity Precedence Name
    | ID_PrefixOperator Precedence Name
    | ID_Name Name
    deriving ()

instance Show Associativity where
    showsPrec prec (A_left) = strstr "left-assoc"
    showsPrec prec (A_right) = strstr "right-assoc"
    showsPrec prec (A_none) = strstr "non-assoc"

instance Eq Identifier where
    id1 == id2 = getNameOfIdentifier id1 == getNameOfIdentifier id2

instance Ord Identifier where
    id1 `compare` id2 = getNameOfIdentifier id1 `compare` getNameOfIdentifier id2

instance Show Identifier where
    showsPrec prec = strstr . getNameOfIdentifier

getNameOfIdentifier :: Identifier -> String
getNameOfIdentifier (ID_InfixOperator _ _ name) = name
getNameOfIdentifier (ID_PrefixOperator _ name) = name
getNameOfIdentifier (ID_Name name) = name

isInfixOp :: Identifier -> Bool
isInfixOp (ID_InfixOperator _ _ _) = True
isInfixOp _ = False

isPrefixOp :: Identifier -> Bool
isPrefixOp (ID_PrefixOperator _ _) = True
isPrefixOp _ = False

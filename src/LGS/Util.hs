module LGS.Util where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type ErrMsg = String

type ParserS = Int

type CharSetVar = String

type RegExVar = String

type HsCode = [String]

type CharSetEnv = Map.Map CharSetVar CharSet

type RegExEnv = Map.Map RegExVar RegEx

data CharSet
    = CsVar CharSetVar
    | CsSingle Char
    | CsEnum Char Char
    | CsUnion CharSet CharSet
    | CsDiff CharSet CharSet
    | CsUniv
    deriving (Eq, Show)

data RegEx
    = ReVar RegExVar
    | ReZero
    | ReUnion RegEx RegEx
    | ReWord String
    | ReConcat RegEx RegEx
    | ReStar RegEx
    | ReDagger RegEx
    | ReQuest RegEx
    | ReCharSet CharSet
    deriving (Eq, Show)

data NFA
    = NFA
        { getInitialQOfNFA :: ParserS
        , getFinalQsOfNFA :: Set.Set ParserS
        , getTransitionsOfNFA :: Map.Map (ParserS, Maybe Char) (Set.Set ParserS)
        , getMarkedQsOfNFA :: Map.Map ParserS ParserS
        }
    deriving (Eq)

data DFA
    = DFA
        { getInitialQOfDFA :: ParserS
        , getFinalQsOfDFA :: Map.Map ParserS ParserS
        , getTransitionsOfDFA :: Map.Map (ParserS, Char) ParserS
        , getMarkedQsOfDFA :: Map.Map ParserS (Set.Set ParserS)
        }
    deriving (Eq)

data XBlock
    = HsHead HsCode
    | HsTail HsCode
    | CsVDef CharSetVar CharSet
    | ReVDef RegExVar RegEx
    | XMatch (RegEx, Maybe RegEx) (Maybe HsCode)
    | Target { getTokenType :: String, getLexerName :: String }
    deriving (Show)

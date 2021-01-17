module PGS.Util where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

type ErrMsg = String

type ProductionRule = (NSym, [Sym])

type ParserS = Int

type HsCode = [String]

data Associativity
    = ALeft
    | ARight
    | ANone
    deriving (Eq, Show)

data NSym
    = NSVar String
    | NSApp NSym NSym
    deriving (Eq, Ord, Show)

data TSym
    = TSEOF
    | TSVar String
    deriving (Eq, Ord, Show)

data Sym
    = NS NSym
    | TS TSym
    deriving (Eq, Ord, Show)

data CFGrammar
    = CFGrammar
        { getStartSym :: NSym
        , getTerminalSyms :: Map.Map TSym (Associativity, Precedence)
        , getProductionRules :: Map.Map ProductionRule Precedence
        }
    deriving (Eq)

data LR0Item
    = LR0Item
        { getLHS :: NSym
        , getLEFT :: [Sym]
        , getRIGHT :: [Sym]
        }
    deriving (Eq, Ord)

data Cannonical0
    = Cannonical0
        { getVertices :: Map.Map (Set.Set LR0Item) ParserS
        , getRoot :: ParserS
        , getEdges :: Map.Map (ParserS, Sym) ParserS
        }
    deriving (Eq)

data Action
    = Shift ParserS
    | Reduce ProductionRule
    | Accept
    deriving (Eq, Show)

data LR1Parser
    = LR1Parser
        { getInitialS :: ParserS
        , getActionTable :: Map.Map (ParserS, TSym) Action
        , getReduceTable :: Map.Map (ParserS, NSym) ParserS
        }
    deriving (Eq)

newtype TerminalSet
    = TerminalSet { unTerminalSet :: Set.Set (Maybe TSym) }
    deriving (Eq)

data Destructor
    = DsStrLit String
    | DsSource String
    | DsNSPatn Int
    | DsTSPatn Int String
    deriving (Show)

data YMatch
    = YMatch
        { getMatchingPrec :: Precedence
        , getMatchingPats :: [Sym]
        , getDestructorss :: [[Destructor]]
        }
    deriving (Show)

data Scheme
    = Scheme
        { getTypeConstr :: Maybe String
        , getSchemeDecl :: (String, String)
        , getParamsDecl :: [(String, String)]
        , getMatchDecls :: [YMatch]
        }
    deriving (Show)

data TerminalInfo
    = TerminalInfo
        { getTerminalPatn :: String
        , getTerminalName :: TSym
        , getTerminalPrec :: Precedence
        , getTerminalAsso :: Associativity
        }
    deriving (Show)

data YTarget
    = YTarget
        { getTokenType :: String
        , getParserName :: String
        , getResultType :: String
        , getStartSymbol :: NSym
        , getTerminalInfos :: [TerminalInfo]
        }
    deriving (Show)

data YBlock
    = HsHead HsCode
    | HsTail HsCode
    | Define Scheme
    | Target YTarget
    deriving (Show)

data Conflict
    = Conflict
        { because :: (Action, Action)
        , whereIs :: (ParserS, TSym)
        , withEnv :: Cannonical0
        }
    deriving ()

instance Semigroup TerminalSet where
    ts1 <> ts2
        | Nothing `Set.member` unTerminalSet ts1 = TerminalSet (Set.delete Nothing (unTerminalSet ts1) `Set.union` unTerminalSet ts2)
        | otherwise = ts1

instance Monoid TerminalSet where
    mempty = TerminalSet (Set.singleton Nothing)

module Butterfly.Back.Executor.Util where

import Butterfly.Back.Base.Instruction
import Butterfly.Back.Base.Util
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

type GmStack = [AdrOf TermNode]

type GmDummy = [(GmStack, GmCode)]

data TermNode
    = NVar (AdrOf TermNode)
    | NCon Tag
    | NFun (AdrOf SC) Arity
    | NApp (AdrOf TermNode) (AdrOf TermNode)
    | NAbs (AdrOf TermNode) (AdrOf TermNode)
    deriving (Eq)

data Executor
    = Executor
        { getNewAdr :: AdrOf TermNode
        , getMemory :: Map.Map (AdrOf TermNode) TermNode
        , loadCodes :: Map.Map (AdrOf SC) GmCode
        }
    deriving ()

data RuntimeErr
    = DerefInvalid (AdrOf TermNode)
    | CannotLoadCodes (AdrOf SC)
    | Unreachable GmCode GmStack GmDummy
    | IsNotNApp TermNode
    deriving ()

malloc :: Monad m => TermNode -> StateT Executor (ExceptT RuntimeErr m) (AdrOf TermNode)
malloc node = do
    executor <- get
    let adr = getNewAdr executor
    put (executor { getNewAdr = adr + 1, getMemory = Map.insert adr node (getMemory executor) })
    return adr

free :: Monad m => AdrOf TermNode -> StateT Executor (ExceptT RuntimeErr m) ()
free adr = do
    executor <- get
    put (executor { getMemory = Map.delete adr (getMemory executor) })
    return ()

deref :: Monad m => AdrOf TermNode -> StateT Executor (ExceptT RuntimeErr m) TermNode
deref adr = do
    executor <- get
    case Map.lookup adr (getMemory executor) of
        Nothing -> lift (throwE (DerefInvalid adr))
        Just node -> return node

update :: Monad m => AdrOf TermNode -> TermNode -> StateT Executor (ExceptT RuntimeErr m) ()
update adr node = do
    executor <- get
    put (executor { getMemory = Map.update (const (Just node)) adr (getMemory executor) })
    return ()

load :: Monad m => AdrOf SC -> StateT Executor (ExceptT RuntimeErr m) GmCode
load fun_adr = do
    executor <- get
    case Map.lookup fun_adr (loadCodes executor) of
        Nothing -> lift (throwE (CannotLoadCodes fun_adr))
        Just code -> return code

rearrange :: Monad m => Arity -> GmStack -> StateT Executor (ExceptT RuntimeErr m) GmStack
rearrange n stack = do
    args <- sequence
        [ do
            node <- deref adr
            case node of
                NApp _ arg -> return arg
                _ -> lift (throwE (IsNotNApp node))
        | adr <- take n stack
        ]
    return (args ++ drop (n - 1) stack)

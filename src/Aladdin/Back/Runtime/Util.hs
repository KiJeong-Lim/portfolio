module Aladdin.Back.Runtime.Util where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.HOPU.Util
import Aladdin.Front.Header
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

type Fact = TermNode

type Goal = TermNode

type Stack = [(Context, [Cell])]

type Satisfied = Bool

type RunMore = Bool

data KernelErr
    = BadGoalGiven TermNode
    | BadFactGiven TermNode
    deriving ()

data Cell
    = Cell
        { _GivenFacts :: [Fact]
        , _ScopeLevel :: ScopeLevel
        , _WantedGoal :: Goal
        }
    deriving ()

data Context
    = Context
        { _TotalVarBinding :: VarBinding
        , _CurrentLabeling :: Labeling
        , _LeftConstraints :: [Disagreement]
        }
    deriving ()

data RuntimeEnv
    = RuntimeEnv
        { _PutStr :: String -> IO ()
        , _Answer :: Context -> IO RunMore
        }
    deriving ()

instance ZonkLVar Cell where
    zonkLVar theta (Cell facts level goal) = Cell (applyBinding theta facts) level (applyBinding theta goal)

showStackItem :: Set.Set LogicVar -> Indentation -> (Context, [Cell]) -> String -> String
showStackItem fvs space (ctx, cells) = strcat
    [ pindent space . strstr "- progressings = " . plist (space + 4) [ strstr "?- " . showsPrec 0 goal | Cell facts level goal <- cells ] . nl
    , pindent space . strstr "- context = Context" . nl
    , pindent (space + 4) . strstr "{ " . strstr "_TotalVarBinding = " . plist (space + 8) [ showsPrec 0 (LVar v) . strstr " +-> " . showsPrec 0 t | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding ctx)), v `Set.member` fvs ] . nl
    , pindent (space + 4) . strstr ", " . strstr "_LeftConstraints = " . plist (space + 8) [ showsPrec 0 constraint | constraint <- _LeftConstraints ctx ] . nl
    , pindent (space + 4) . strstr "} " . nl
    ]

showsCurrentState :: Set.Set LogicVar -> Context -> [Cell] -> Stack -> String -> String
showsCurrentState fvs ctx cells stack = strcat
    [ strstr "* The top of the stack is:" . nl
    , showStackItem fvs 4 (ctx, cells) . nl
    , strstr "* The rest of the stack is:" . nl
    , strcat
        [ strcat
            [ pindent 2 . strstr "- #[ " . showsPrec 0 i . strstr "]:" . nl
            , showStackItem fvs 4 item . nl
            ]
        | (i, item) <- zip [1, 2 .. length stack] stack
        ]
    , strstr "--------------------------------" . nl
    ]

mkCell :: [Fact] -> ScopeLevel -> Goal -> Cell
mkCell facts level goal = goal `seq` Cell { _GivenFacts = facts, _ScopeLevel = level, _WantedGoal = goal }

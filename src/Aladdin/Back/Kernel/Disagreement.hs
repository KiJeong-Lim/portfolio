module Aladdin.Back.Kernel.Disagreement where

import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Show
import Aladdin.Back.Base.VarBinding
import Lib.Base

infix 6 :=?=:

data Disagreement
    = TermNode :=?=: TermNode
    deriving (Eq)

instance Show Disagreement where
    showList = ppunc "\n" . map (showsPrec 0)
    showsPrec _ (lhs :=?=: rhs) = showsPrec 0 lhs . strstr " =?= " . showsPrec 0 rhs

instance HasLVar Disagreement where
    getFreeLVars (lhs :=?=: rhs) = getFreeLVars lhs . getFreeLVars rhs
    applyBinding theta (lhs :=?=: rhs) = applyBinding theta lhs :=?=: applyBinding theta rhs

module Butterfly.Back.Base.Util where

import Data.Unique
import Lib.Base

type ErrMsg = String

type Tag = LargeId

type Arity = Int

type SmallId = String

type IsRec = Bool

type SC = SmallId

type IVar = String

newtype LargeId
    = LargeId { unLargeId :: String }
    deriving (Eq, Ord)

class HasAnnot f where
    getAnnot :: f a -> a

instance Show LargeId where
    showsPrec _ = showsPrec 0 . unLargeId

instance Outputable LargeId where
    pprint _ = showsPrec 0 . unLargeId

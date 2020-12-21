module Lib.Text.PC where

import Control.Applicative
import Control.Monad
import qualified Data.Set as Set
import Lib.Algorithm.Sorting
import Lib.Text.PC.Base
import Lib.Text.PC.Check
import Lib.Text.PC.Loc
import Lib.Text.PC.Regex
import Test.QuickCheck
import Test.QuickCheck.Checkers

infix 9 <?>

type NameOfPC = String

newtype PC val
    = PC { unPC :: ParserBase ParserErr LocChr val }
    deriving ()

instance Functor PC where
    fmap a2b = PC . fmap a2b . unPC

instance Applicative PC where
    pure = PC . pure
    p1 <*> p2 = PC (unPC p1 <*> unPC p2)

instance Monad PC where
    p1 >>= p2 = PC (unPC p1 >>= unPC . p2)

instance Alternative PC where
    empty = PC empty
    p1 <|> p2 = PC (unPC p1 <|> unPC p2)

instance MonadPlus PC where

instance Semigroup (PC val) where
    p1 <> p2 = PC (unPC p1 <> unPC p2)

instance Monoid (PC val) where
    mempty = PC mempty

instance Eq val => EqProp (PC val) where
    p1 =-= p2 = unPC p1 =-= unPC p2

instance Arbitrary val => Arbitrary (PC val) where
    arbitrary = fmap PC arbitrary

instance Show val => Show (PC val) where
    showsPrec prec = showsPrec prec . unPC

(<?>) :: NameOfPC -> PC val -> PC val
name1 <?> p1 = PC (go (unPC p1)) where
    go :: ParserBase ParserErr LocChr val -> ParserBase ParserErr LocChr val
    go p = PAct $ \str0 -> case unPB p str0 of
        Left err -> PAlt (Set.insert name1 err) []
        Right pairs -> PAlt (Set.singleton name1) pairs

autoPC :: Read val => NameOfPC -> PC val
autoPC expecteds = PC go where
    go :: Read val => ParserBase ParserErr LocChr val
    go = PAct $ \lstr0 -> PAlt (Set.singleton ("`autoPC " ++ show expecteds ++ "\' failed.")) [ (PVal val1, drop (length lstr0 - length str1) lstr0) | (val1, str1) <- readsPrec 0 (map snd lstr0) ]

acceptPC :: (Char -> Bool) -> PC Char
acceptPC cond = PC go where
    go :: ParserBase ParserErr LocChr Char
    go = PAct $ \lstr -> case lstr of
        ((r, c), ch) : lstr'
            | cond ch -> PAlt Set.empty [(PVal ch, lstr')]
        _ -> PAlt Set.empty []

consumePC :: String -> PC ()
consumePC expecteds = ("`consumePC " ++ show expecteds ++ "\' failed.") <?> mapM_ acceptPC (map (==) expecteds)

matchPC :: String -> PC ()
matchPC expecteds = ("`matchPC " ++ show expecteds ++ "\' failed.") <?> PC go where
    go :: ParserBase ParserErr LocChr ()
    go = PAct $ \lstr0 -> if expecteds == map snd (take (length expecteds) lstr0)
        then PAlt Set.empty [(PVal (), drop (length expecteds) lstr0)]
        else PAlt Set.empty []

eofPC :: PC ()
eofPC = PC go where
    go :: ParserBase ParserErr LocChr ()
    go = PAct $ \lstr0 -> if null lstr0
        then PAlt Set.empty [(PVal (), lstr0)]
        else PAlt (Set.singleton "`eofPC\' failed.") []

regexPC :: RegExRep -> PC String
regexPC = PC . parserOfRegularExpression

negPC :: PC a -> PC ()
negPC = PC . negPB . unPC

runPC :: PC val -> Src -> Either ErrMsg val
runPC p str0 = case runPB (unPC p) (addLoc str0) of
    Left pair -> Left (mkErrMsg str0 pair)
    Right pairs -> case [ val | (val, lstr1) <- pairs, null lstr1 ] of
        [] -> Left (mkErrMsg str0 (Set.singleton "must be EOF.", head (sortByMerging (\lstr1 -> \lstr2 -> length lstr1 <= length lstr2) (map snd pairs))))
        val : _ -> Right val

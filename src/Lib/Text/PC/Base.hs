module Lib.Text.PC.Base where

import Control.Applicative
import Control.Monad
import Lib.Algorithm.Sorting
import Lib.Text.Ppr

data ParserBase err chr val
    = PVal
        val
    | PAlt
        err
        [(ParserBase err chr val, [chr])]
    | PAct
        ([chr] -> ParserBase err chr val)
    deriving ()

instance Functor (ParserBase err chr) where
    fmap a2b p1 = bindPB p1 (returnPB . a2b)

instance Applicative (ParserBase err chr) where
    pure = returnPB
    p1 <*> p2 = bindPB p1 (flip fmap p2)

instance Monad (ParserBase err chr) where
    p1 >>= p2 = bindPB p1 p2

instance Monoid err => Alternative (ParserBase err chr) where
    empty = emptyPB
    p1 <|> p2 = appendPB p1 p2

instance Monoid err => MonadPlus (ParserBase err chr) where

instance Monoid err => Semigroup (ParserBase err chr val) where
    (<>) = (<|>)

instance Monoid err => Monoid (ParserBase err chr val) where
    mempty = empty

instance (Show err, Show chr, Show val) => Show (ParserBase err chr val) where
    show = flip (showsPrec 0) ""
    showList [] str = "[]" ++ str
    showList (x : xs) str = "[" ++ go x xs str where
        go :: (Show err, Show chr, Show val) => ParserBase err chr val -> [ParserBase err chr val] -> String -> String
        go p1 [] str = showsPrec 0 p1 ("]" ++ str)
        go p1 (p2 : ps) str = showsPrec 0 p1 ("," ++ go p2 ps str)
    showsPrec prec = go where
        parenthesize :: Int -> (String -> String) -> String -> String
        parenthesize prec' strstr str
            | prec > prec' = "(" ++ strstr (")" ++ str)
            | otherwise = strstr str
        go :: (Show err, Show chr, Show val) => ParserBase err chr val -> String -> String
        go (PVal val1) = parenthesize 9 (\str -> "PVal " ++ showsPrec 10 val1 str)
        go (PAlt err1 alts1) = parenthesize 9 (\str -> "PAct " ++ showsPrec 10 err1 (" " ++ showList alts1 str))
        go (PAct act1) = parenthesize 9 (\str -> "PAct ([] +-> " ++ showsPrec 0 (act1 []) (")" ++ str))

unPB :: ParserBase err chr val -> [chr] -> Either err [(ParserBase err chr val, [chr])]
unPB (PVal val1) str0 = Right [(PVal val1, str0)]
unPB (PAlt err1 alts1) str0
    | null alts1 = Left err1
    | otherwise = Right alts1
unPB (PAct act1) str0 = unPB (act1 str0) str0

returnPB :: val -> ParserBase err chr val
returnPB val1 = PVal val1

bindPB :: ParserBase err chr val1 -> (val1 -> ParserBase err chr val2) -> ParserBase err chr val2
bindPB (PVal val1) p2 = p2 val1
bindPB (PAlt err1 alts1) p2 = PAlt err1 [ (bindPB p1 p2, str1) | (p1, str1) <- alts1 ]
bindPB (PAct act1) p2 = PAct $ \str0 -> bindPB (act1 str0) p2

emptyPB :: Monoid err => ParserBase err chr val
emptyPB = PAlt mempty []

appendPB :: Monoid err => ParserBase err chr val -> ParserBase err chr val -> ParserBase err chr val
appendPB = go where
    go :: Monoid err => ParserBase err chr val -> ParserBase err chr val -> ParserBase err chr val
    go (PAlt err1 []) (PAlt err2 []) = PAlt (err1 <> err2) []
    go (PAlt err1 []) p2 = p2
    go p1 (PAlt err2 []) = p1
    go p1 p2 = PAct $ \str0 -> case (unPB p1 str0, unPB p2 str0) of
        (Left err1, Left err2) -> PAlt (err1 <> err2) []
        (Left err1, Right alts2) -> PAlt mempty alts2
        (Right alts1, Left err2) -> PAlt mempty alts1
        (Right alts1, Right alts2) -> PAlt mempty (alts1 ++ alts2)

mkPB :: ([chr] -> [(val, [chr])]) -> err -> ParserBase err chr val
mkPB _ReadS err1 = PAct $ \str0 -> PAlt err1 [ (PVal val1, str1) | (val1, str1) <- _ReadS str0 ]

negPB :: Monoid err => ParserBase err chr val -> ParserBase err chr ()
negPB (PAlt err1 []) = pure ()
negPB p1 = PAct $ \str0 -> case unPB p1 str0 of
    Left err1 -> PAlt mempty [(PVal (), str0)]
    Right alts1 -> PAlt mempty []

runPB :: Monoid err => ParserBase err chr val -> [chr] -> Either (err, [chr]) [(val, [chr])]
runPB = flip go (mempty, []) where
    findShortest :: [(err, [chr])] -> (err, [chr])
    findShortest = head . sortByMerging (\x1 -> \x2 -> length (snd x1) <= length (snd x2))
    go :: Monoid err => ParserBase err chr val -> (err, [chr]) -> [chr] -> Either (err, [chr]) [(val, [chr])]
    go (PVal val1) (err0, es0) str0 = Right [(val1, str0)]
    go (PAlt err1 alts1) (err0, es0) str0
        = case [ go p1 (err0 <> err1, str1) str1 | (p1, str1) <- alts1 ] of
            [] -> Left (err1, es0)
            results -> case [ (val2, str2) | Right pairs <- results, (val2, str2) <- pairs ] of
                [] -> Left (findShortest [ (err2, es2) | Left (err2, es2) <- results ])
                pairs -> Right pairs
    go (PAct act1) (err0, es0) str0 = go (act1 str0) (mempty, str0) str0

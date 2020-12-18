module Lib.Text.PC.Expansion where

import Control.Applicative
import Control.Monad
import qualified Data.Set as Set
import Lib.Algorithm.Sorting
import Lib.Text.PC
import Lib.Text.PC.Base
import Lib.Text.PC.Check
import Lib.Text.PC.Loc
import Lib.Text.PC.Regex

acceptQuote :: PC String
acceptQuote = PC go where
    loop :: LocStr -> Either LocStr (String, LocStr)
    loop lstr0 = case map snd (take 1 lstr0) of
        [] -> Left lstr0
        ['\\'] -> case map snd (take 1 (drop 1 lstr0)) of
            ['\"'] -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\"' : quote, lstr1)
            ['\''] -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\'' : quote, lstr1)
            ['\\']  -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\\' : quote, lstr1)
            ['\n']  -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\n' : quote, lstr1)
            ['\t']  -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\t' : quote, lstr1)
            _ -> Left lstr0
        ['\n'] -> Left lstr0
        ['\t'] -> Left lstr0
        ['\"'] -> return ("", drop 1 lstr0)
        [ch] -> do
                (quote, lstr1) <- loop (drop 1 lstr0)
                return (ch : quote, lstr1)
    go :: ParserBase ParserErr LocChr String
    go = PAct $ \lstr0 -> case lstr0 of
        (_, '\"') : lstr1 -> case loop lstr1 of
            Left lstr2 -> PAlt (Set.singleton "acceptQuote") []
            Right (quote, lstr2) -> PAlt mempty [(PVal quote, lstr2)]
        lstr1 -> PAlt (Set.singleton "acceptQuote") []

skipWhite :: PC ()
skipWhite = PC go where
    go :: ParserBase ParserErr LocChr ()
    go = PAct $ \lstr0 -> PAlt mempty [(PVal (), dropWhile (\lch -> snd lch == ' ') lstr0)]

lend :: PC ()
lend = skipWhite *> consumePC "\n"

indent :: Int -> PC ()
indent n = consumePC space where
    space :: String
    space = replicate n ' '

smallid :: PC String
smallid = regexPC "[\'a\'-\'z\'] [\'a\'-\'z\' \'0\'-\'9\' \'_\']*"

largeid :: PC String
largeid = regexPC "[\'A\'-\'Z\'] [\'a\'-\'z\' \'0\'-\'9\' \'A\'-\'Z\']*"

module Lib.Text.PC.Regex where

import Control.Applicative
import Control.Monad
import qualified Data.List as List
import qualified Data.Set as Set
import Lib.Algorithm.Sorting
import Lib.Base
import Lib.Text.PC.Base
import Lib.Text.PC.Loc

type RegExRep = String

data CharSet
    = CsUniv
    | CsUnion CharSet CharSet
    | CsDiff CharSet CharSet
    | CsEnum Char Char
    | CsSingle Char
    deriving ()

data RegEx
    = ReCharSet CharSet
    | ReWord String
    | RePlus RegEx RegEx
    | ReZero
    | ReMult RegEx RegEx
    | ReStar RegEx
    deriving ()

instance Read CharSet where
    readsPrec = runPM . go where
        go :: Int -> PM CharSet
        go 0 = List.foldl' CsDiff <$> go 1 <*> many (consumeStr "\\" *> go 2)
        go 1 = List.foldl' CsUnion <$> go 2 <*> many (consumeStr " " *> go 2)
        go 2 = mconcat
            [ CsSingle <$> autoPM 0
            , CsEnum <$> autoPM 0 <* consumeStr "-" <*> autoPM 0
            , consumeStr "." *> pure CsUniv
            , go 3
            ]
        go _ = consumeStr "(" *> go 0 <* consumeStr ")"
    readList = undefined

instance Read RegEx where
    readsPrec = runPM . go where
        suffix :: Int -> PM (RegEx -> RegEx)
        suffix 2 = mconcat
            [ consumeStr "*" *> pure (\re -> ReStar re)
            , consumeStr "+" *> pure (\re -> ReMult re (ReStar re))
            , consumeStr "?" *> pure (\re -> RePlus re (ReWord ""))
            ]
        suffix _ = empty
        go :: Int -> PM RegEx
        go 0 = List.foldl' RePlus <$> go 1 <*> many (consumeStr " + " *> go 1)
        go 1 = List.foldl' ReMult <$> go 2 <*> many (consumeStr " " *> go 2)
        go 2 = List.foldl' (flip ($)) <$> go 3 <*> many (suffix 2)
        go 3 = mconcat
            [ consumeStr "[" *> (ReCharSet <$> autoPM 0) <* consumeStr "]"
            , pure ReWord <* matchPrefix "\"" <*> autoPM 0
            , consumeStr "()" *> pure ReZero
            , go 4
            ]
        go _ = consumeStr "(" *> go 0 <* consumeStr ")"
    readList = undefined

parserOfRegularExpression :: RegExRep -> ParserBase ParserErr LocChr String
parserOfRegularExpression regex_rep = go maybeRegEx where
    maybeRegEx :: Maybe RegEx
    maybeRegEx
        = case [ regex | (regex, "") <- readsPrec 0 regex_rep ] of
            [regex] -> Just regex
            _ -> Nothing
    runCharSet :: CharSet -> Char -> Bool
    runCharSet CsUniv ch = True
    runCharSet (CsUnion chs1 chs2) ch = runCharSet chs1 ch || runCharSet chs2 ch
    runCharSet (CsDiff ch1 ch2) ch = runCharSet ch1 ch && not (runCharSet ch2 ch)
    runCharSet (CsEnum ch1 ch2) ch = ch1 <= ch && ch <= ch2
    runCharSet (CsSingle ch1) ch = ch == ch1
    runRegEx :: RegEx -> LocStr -> [(String, LocStr)]
    runRegEx (ReCharSet chs) lstr0 = case lstr0 of
        lch1 : lstr1
            | runCharSet chs (snd lch1) -> [([snd lch1], lstr1)]
        _ -> []
    runRegEx (ReWord str) lstr0
        | str == map snd (take (length str) lstr0) = [(str, drop (length str) lstr0)]
        | otherwise = []
    runRegEx (RePlus regex1 regex2) lstr0 = runRegEx regex1 lstr0 ++ runRegEx regex2 lstr0
    runRegEx ReZero lstr0 = []
    runRegEx (ReMult regex1 regex2) lstr0 = [ (str1 ++ str2, lstr2) | (str1, lstr1) <- runRegEx regex1 lstr0, (str2, lstr2) <- runRegEx regex2 lstr1 ]
    runRegEx (ReStar regex1) lstr0 = ("", lstr0) : [ (str1 ++ str2, lstr2) | (str1, lstr1) <- runRegEx regex1 lstr0, (str2, lstr2) <- runRegEx (ReStar regex1) lstr1 ]
    orderResult :: (String, LocStr) -> (String, LocStr) -> Bool
    orderResult (str1, lstr1) (str2, lstr2) = length str1 > length str2
    go :: Maybe RegEx -> ParserBase ParserErr LocChr String
    go Nothing = error ("wrong regex: " ++ show regex_rep)
    go (Just regex) = PAct $ \lstr0 -> case sortByMerging orderResult (runRegEx regex lstr0) of
        [] -> PAlt (Set.singleton ("regexPM " ++ show regex_rep)) []
        (str1, lstr1) : _ -> PAlt Set.empty [(PVal str1, lstr1)]

module Lib.Text.PC.Loc where

import qualified Data.Set as Set
import Lib.Text.Ppr

type Row = Int

type Col = Int

type Loc = (Row, Col)

type LocChr = (Loc, Char)

type LocStr = [LocChr]

type ParserErr = Set.Set String

type Src = String

type ErrMsg = String

addLoc :: Src -> LocStr
addLoc = go 1 1 where
    getNextRow :: Row -> Char -> Row
    getNextRow r '\n' = r + 1
    getNextRow r _ = r
    getNextCol :: Col -> Char -> Col
    getNextCol c '\n' = 1
    getNextCol c '\t' = c + 8
    getNextCol c _ = c + 1
    go :: Row -> Col -> String -> LocStr
    go r c [] = []
    go r c (ch : str) = ((r, c), ch) : go (getNextRow r ch) (getNextCol c ch) str

mkErrMsg :: Src -> (ParserErr, LocStr) -> ErrMsg
mkErrMsg src (err, lstr) = renderDoc err_msg where
    splitBy :: Char -> String -> [String]
    splitBy ch = loop where
        loop :: String -> [String]
        loop [] = [""]
        loop (ch1 : str1)
            | ch == ch1 = "" : loop str1
            | otherwise = case loop str1 of
                str : strs -> (ch1 : str) : strs
    stuck_row :: Row
    stuck_row = case lstr of
        [] -> length (filter (\lch -> snd lch == '\n') lstr) + 1
        ((r, c), _) : _ -> r
    stuck_line :: Src
    stuck_line = splitBy '\n' src !! (stuck_row - 1)
    stuck_col :: Col
    stuck_col = case lstr of
        [] -> length stuck_line + 1
        ((r, c), _) : _ -> c
    err_msg :: Doc
    err_msg = vconcat
        [ blue (text "parsing error at " <> pprint 0 stuck_row <> text ":" <> pprint 0 stuck_col <> text ".")
        , hconcat
            [ vconcat
                [ text ""
                , blue (text " " <> pprint 0 stuck_row <> text " ")
                , text ""
                ]
            , blue mkBeam
            , vconcat
                [ text ""
                , text " " <> red (text stuck_line)
                , case lstr of
                    [] -> mempty
                    ((r, c), _) : _ -> white c <> red (text "^")
                ]
            ]
        , blue (text "?- because:")
        , indent 1
            [ red (text "- " <> text pc)
            | pc <- Set.toList err
            ]
        ]

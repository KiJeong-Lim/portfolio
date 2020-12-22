module Aladdin.Back.Base.TermNode.Read where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.TermNode
import Aladdin.Front.Header
import Control.Applicative
import qualified Data.List as List
import Lib.Base

instance Read TermNode where
    readsPrec = runPM . flip go [] where
        readVar :: [LargeId] -> PM TermNode
        readVar env = do
            ch1 <- acceptCharIf (\ch -> ch `elem` ['A' .. 'Z'])
            str1 <- many (acceptCharIf (\ch -> ch `elem` ['A' .. 'Z'] || ch `elem` ['a' .. 'z'] || ch `elem` ['0' .. '9']))
            let name1 = ch1 : str1
            case name1 `List.elemIndex` env of
                Nothing -> return (mkLVar (LV_Named name1))
                Just i -> return (mkNIdx (i + 1))
        readIVar :: PM LargeId
        readIVar = do
            ch1 <- acceptCharIf (\ch -> ch `elem` ['A' .. 'Z'])
            str1 <- many (acceptCharIf (\ch -> ch `elem` ['A' .. 'Z'] || ch `elem` ['a' .. 'z'] || ch `elem` ['0' .. '9']))
            return (ch1 : str1)
        readCon :: PM TermNode
        readCon = do
            ch1 <- acceptCharIf (\ch -> ch `elem` ['a' .. 'z'])
            str1 <- many (acceptCharIf (\ch -> ch `elem` ['a' .. 'z'] || ch `elem` ['0' .. '9'] || ch `elem` ['_']))
            let name1 = ch1 : str1
            return (mkNCon (DC_Named name1))
        go :: Precedence -> [LargeId] -> PM TermNode
        go 0 vs = mconcat
            [ do
                v <- readIVar
                consumeStr "\\ "
                t <- go 0 (v : vs)
                return (mkNAbs t)
            , go 1 vs
            ]
        go 1 vs = do
            t <- go 2 vs
            ts <- many (consumeStr " " *> go 2 vs)
            return (List.foldl' mkNApp t ts)
        go _ vs = mconcat
            [ readCon
            , readVar vs
            , consumeStr "(" *> go 0 vs <* consumeStr ")"
            ]

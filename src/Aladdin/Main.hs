module Main where

import Aladdin.Front.Analyzer.Grammar
import Aladdin.Front.Analyzer.Lexer
import Aladdin.Front.Analyzer.Parser
import Aladdin.Front.Header
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

main :: IO ()
main = undefined

analyzer :: String -> Either ErrMsg AnalyzerOuput
analyzer src0
    = case runAladdinLexer src0 of
        Left (row, col) -> Left ("lexing error at { row = " ++ showsPrec 0 row (", col = " ++ showsPrec 0 col " }."))
        Right src1 -> case runAladdinParser src1 of
            Left Nothing -> Left ("parsing error at EOF.")
            Left (Just token) -> case getSLoc token of
                SLoc (row1, col1) (row2, col2) -> Left ("parsing error at { row = " ++ showsPrec 0 row1 (", col = " ++ showsPrec 0 col1 " }."))
            Right output -> Right output

readSource :: FilePath -> IO (Either ErrMsg AnalyzerOuput)
readSource dir = do
    src <- readFile dir
    let result = analyzer src
    result `seq` return result

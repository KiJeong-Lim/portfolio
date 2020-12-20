module Main where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base
import LGS.Read
import LGS.Show
import LGS.Util
import Lib.Text.PC
import Lib.Text.PC.Expansion

runLGS :: FilePath -> IO ()
runLGS dir = do
    x_src <- readFile dir
    case runPC (many (readBlock <* many lend)) x_src of
        Left err -> putStrLn err
        Right xblocks -> case runIdentity (runExceptT (genLexer xblocks)) of
            Left err -> putStrLn err
            Right delta -> do
                writeFile (dir ++ ".hs") (delta "")
                putStrLn "the lexer has been generated."
                return ()

main :: IO ()
main = do
    putStrLn "enter the path:"
    dir <- getLine
    runLGS dir

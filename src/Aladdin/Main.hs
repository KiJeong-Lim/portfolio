module Main where

import Aladdin.Back.BackEnd
import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Show
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Converter.Main
import Aladdin.Back.HOPU.Util
import Aladdin.Back.Runtime.Main
import Aladdin.Back.Runtime.Util
import Aladdin.Front.Analyzer.Main
import Aladdin.Front.Desugarer.Main
import Aladdin.Front.Header
import Aladdin.Front.TypeChecker.Main
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit

showCopyright :: String
showCopyright = concat
    [ "Copyright (c) 2020, KiJeong-Lim\n"
    , "All rights reserved.\n"
    ]

runAladdin :: IO ()
runAladdin = do
    putStrLn "Enter the path of the aladdin file to execute:"
    dir <- getLine
    src <- readFile dir
    case runAnalyzer src of
        Left err_msg -> do
            putStrLn err_msg
            runAladdin
        Right output -> case output of
            Left query1 -> do
                putStrLn "parsing-error: it is not a program."
                runAladdin
            Right program1 -> runUniqueGenT $ do
                result <- runExceptT $ do
                    module1 <- desugarProgram theInitialKindEnv theInitialTypeEnv program1
                    facts2 <- sequence [ checkType (_TypeDecls module1) fact mkTyO | fact <- _FactDecls module1 ]
                    facts3 <- sequence [ convertProgram used_mtvs assumptions fact | (fact, (used_mtvs, assumptions)) <- facts2 ]
                    let kind_env = _KindDecls module1
                        type_env = _TypeDecls module1
                    kind_env `seq` type_env `seq` facts3 `seq` return (Program { _KindDecls = kind_env, _TypeDecls = type_env, _FactDecls = facts3 })
                case result of
                    Left err_msg -> lift $ do
                        putStrLn err_msg
                        runAladdin
                    Right program2 -> do
                        lift $ putStrLn ("Loaded: " ++ dir)
                        runREPL program2

main :: IO ()
main = do
    putStrLn showCopyright
    runAladdin

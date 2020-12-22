module Aladdin.Back.BackEnd where

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
import Data.IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit

type Debugging = Bool

quitWithMsg :: String -> IO ()
quitWithMsg str = do
    putStrLn str
    exitSuccess

runREPL :: Program TermNode -> UniqueGenT IO ()
runREPL program = lift (newIORef False) >>= go where
    mkRuntimeEnv :: IORef Debugging -> TermNode -> IO RuntimeEnv
    mkRuntimeEnv isDebugging query = return (RuntimeEnv { _PutStr = runInteraction, _Answer = printAnswer }) where
        runInteraction :: String -> IO ()
        runInteraction str = do
            debugging <- readIORef isDebugging
            if debugging
                then do
                    putStrLn str
                    response <- getLine
                    case response of
                        ":q" -> quitWithMsg ""
                        ":d" -> modifyIORef isDebugging not
                        _ -> return ()
                else return ()
        printAnswer :: Context -> IO RunMore
        printAnswer final_ctx
            | isShort && isClear = return False
            | isShort = do
                printDisagreements
                askToRunMore
            | otherwise = do
                putStrLn "The answer substitution is:"
                sequence
                    [ putStrLn ("  " ++ v ++ " := " ++ showsPrec 0 t ".")
                    | (LV_Named v, t) <- Map.toList (unVarBinding (_TotalVarBinding final_ctx))
                    ]
                if isClear
                    then return ()
                    else printDisagreements
                askToRunMore
            where
                isShort :: Bool
                isShort = Set.null (getFreeLVs query)
                isClear :: Bool
                isClear = List.null (_LeftConstraints final_ctx)
                askToRunMore :: IO RunMore
                askToRunMore = do
                    putStrLn "Find more solutions?"
                    str <- getLine
                    if str == "Y" || str == "y"
                        then return False
                        else return True
                printDisagreements :: IO ()
                printDisagreements = do
                    putStrLn "The remaining disagreements are:"
                    sequence
                        [ putStrLn ("  " ++ showsPrec 0 lhs (" =?= " ++ showsPrec 0 rhs "."))
                        | lhs :=?=: rhs <- _LeftConstraints final_ctx
                        ]
                    putStrLn "The binding is:"
                    sequence
                        [ putStrLn ("  " ++ showsPrec 0 (mkLVar v) (" +-> " ++ showsPrec 0 t "."))
                        | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding final_ctx))
                        ]
                    return ()
    go :: IORef Debugging -> UniqueGenT IO ()
    go isDebugging = do
        query0 <- lift $ getLine
        case query0 of
            "" -> lift $ quitWithMsg ""
            ":q" -> lift $ quitWithMsg "bye."
            ":d" -> do
                lift $ do
                    modifyIORef isDebugging not
                    debugging <- readIORef isDebugging
                    putStrLn ("Debugging mode " ++ (if debugging then "on" else "off") ++ ".")
                go isDebugging
            query0 -> case runAnalyzer query0 of
                Left err_msg -> do
                    lift $ putStrLn err_msg
                    go isDebugging
                Right output -> case output of
                    Left query1 -> do
                        result <- runExceptT $ do
                            (query2, free_vars) <- desugarQuery query1
                            (query3, (used_mtvs, assumptions)) <- checkType (_TypeDecls program) query2 mkTyO
                            convertQuery used_mtvs assumptions (Map.fromList [ (ivar, mkLVar (LV_Named name)) | (name, ivar) <- Map.toList free_vars ]) query3
                        case result of
                            Left err_msg -> do
                                lift $ putStrLn err_msg
                                go isDebugging
                            Right query4 -> do
                                runtime_env <- lift $ mkRuntimeEnv isDebugging query4
                                answer <- runExceptT (execRuntime runtime_env (_FactDecls program) query4)
                                case answer of
                                    Left runtime_err -> case runtime_err of
                                        BadGoalGiven _ -> lift $ putStrLn "runtime-error: bad goal given!"
                                        BadFactGiven _ -> lift $ putStrLn "runtime-error: bad fact given!"
                                    Right sat -> lift $ putStrLn (if sat then "yes." else "no.")
                                go isDebugging
                    Right src1 -> do
                        lift $ putStrLn "parsing-error: it is not a query!"
                        go isDebugging

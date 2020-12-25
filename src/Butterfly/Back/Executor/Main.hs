{-# LANGUAGE ForeignFunctionInterface #-}
module Butterfly.Back.Executor.Main where

import Foreign.C.String
foreign import ccall "execute" c_execute :: CString -> IO CInt

runExecutor :: FilePath -> IO Bool
runExecutor dir = do
    c_dir <- newCAString dir
    c_res <- c_execute c_dir
    case toInteger c_res of
        0 -> return True
        _ -> return False

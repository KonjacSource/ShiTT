module Main (main) where

import System.Environment(getArgs)
import ShiTT.Parser 

main :: IO ()
main = do 
  args <- getArgs
  case args of 
    ["repl"] -> repl
    [fp] -> run fp
    _ -> putStrLn "Unkown arguments"
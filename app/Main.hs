module Main (main) where

import System.Environment(getArgs)
import ShiTT.Parser 

main :: IO ()
main = do 
  fp <- getArgs
  run $ head fp
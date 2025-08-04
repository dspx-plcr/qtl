module Main where

import Data.Function

import Error
import Parser
import Reader
import Source

main :: IO ()
main = do
  prog <- readFile "prog"
  prog & Reader.read >>= Parser.parse & \case
    Left err -> putStrLn (buildMessage err)
    Right prog -> putStrLn (Parser.pp prog)

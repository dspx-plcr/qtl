module Main where

import Error
import Reader
import Source

main :: IO ()
main = do
  prog <- readFile "prog"
  case Reader.read prog of
    Left err -> putStrLn (buildMessage err)
    Right prog -> putStrLn (Reader.pp prog)

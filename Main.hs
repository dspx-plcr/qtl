module Main where

import Data.Function

import Error
import Parser
import Reader
import Source
import Typer

main :: IO ()
main = do
  prog <- readFile "prog"
  prog & Reader.read >>= Parser.parse >>= Typer.typecheck & \case
    Left err -> putStrLn (buildMessage err)
    Right prog -> putStrLn (Typer.pp prog)

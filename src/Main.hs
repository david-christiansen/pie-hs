module Main where

import System.IO

import Pie.Elab
import Pie.Parse
import Pie.Types

main =
  do hSetBuffering stdout NoBuffering
     repl


repl :: IO ()
repl =
  do putStr "Π> "
     l <- getLine
     let e = testParser expr l
     case e of
       Left err -> print err
       Right expr ->
         print $ runElab (isType expr) None (Loc "<interactive>" (Pos 1 0) (Pos 1 (length l)))
     main

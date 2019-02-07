module Main where

import qualified Data.Text.IO as T
import System.IO

import Pie.Elab
import Pie.Output
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
         case runElab (isType expr) None (Loc "<interactive>" (Pos 1 0) (Pos 1 (length l))) [] of
           Left _ ->
             case runElab (toplevel expr) None (Loc "<interactive>" (Pos 1 0) (Pos 1 (length l))) [] of
               Left err -> print err
               Right e ->
                 T.putStrLn (pp (resugar e))
           Right ok -> T.putStrLn (pp (resugar ok))
     main

module Main where

import Data.Traversable
import qualified Data.Text.IO as T
import System.IO

import Pie.Elab
import Pie.Output
import Pie.Parse
import Pie.Types

main =
  do hSetBuffering stdout NoBuffering
     repl

dumpInfo infos =
  traverse (T.putStrLn . dumpLocElabInfo) infos *> pure ()

repl :: IO ()
repl =
  do putStr "Π> "
     l <- getLine
     let e = testParser expr l
     case e of
       Left err -> print err
       Right expr ->
         case runElab (isType expr) None (Loc "<interactive>" (Pos 1 0) (Pos 1 (length l))) [] of
           (_, Left _) ->
             case runElab (toplevel expr) None (Loc "<interactive>" (Pos 1 0) (Pos 1 (length l))) [] of
               (infos, Left err) -> print err *> dumpInfo infos
               (infos, Right e) ->
                 do T.putStrLn (pp (resugar e))
                    dumpInfo infos
           (infos, Right ok) ->
             do T.putStrLn (pp (resugar ok))
                dumpInfo infos
     main

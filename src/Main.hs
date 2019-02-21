module Main where

import Data.List
import Data.Traversable
import qualified Data.Text.IO as T
import System.IO

import Pie.Elab (Ctx)
import Pie.Output
import Pie.Parse
import Pie.TopLevel
import Pie.Types

main =
  do hSetBuffering stdout NoBuffering
     repl (TopState None [])

dumpInfo infos =
  traverse (T.putStrLn . dumpLocElabInfo)
    (sortBy (\x y -> compare (getLoc x) (getLoc y)) infos) *>
  pure ()

repl :: TopState -> IO ()
repl st =
  do putStr "Π> "
     l <- getLine
     if l == ":dump"
       then print st *> repl st
       else do let e = testParser topLevel l
               case e of
                 Left err -> print err
                 Right parsed@(Located loc _) ->
                   do let (info, res) = runTopElab (top parsed) st loc
                      dumpInfo info
                      case res of
                        Left err ->
                          do print err
                             repl st
                        Right ((), st') ->
                          repl st'

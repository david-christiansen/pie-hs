module Main where

import Data.List
import Data.Traversable
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.Environment
import System.Exit
import System.IO

import Pie.Elab (Ctx)
import Pie.Output
import Pie.Parse
import Pie.TopLevel
import Pie.Types

main =
  do hSetBuffering stdout NoBuffering
     args <- getArgs
     case args of
       [] ->
         do sayHello
            repl (TopState None [])
       [file] ->
         processFile file
       more ->
         do printUsage
            exitFailure

sayHello =
  do putStrLn "   _______ _    __  "
     putStrLn "  / /  __ (_)   \\ \\ "
     putStrLn " | || |__) |  ___| |"
     putStrLn " | ||  ___/ |/ _ \\ |"
     putStrLn " | || |   | || __/ |"
     putStrLn " | ||_|   |_|\\___| |"
     putStrLn "  \\_\\           /_/ "
     putStrLn ""
     putStrLn "Pre-release! It's not done!"
     putStrLn ""

printUsage =
  do putStrLn "Usage:"
     putStrLn "\t pie\tRun the Pie REPL"
     putStrLn "\t pie FILE\tLoad FILE in Pie"

endPos :: Text -> Pos
endPos input = Pos l c
  where
    lines = T.lines input
    l = max 1 (length lines)
    c = case lines of
          [] -> 1
          more -> T.length (last more)


processFile :: FilePath -> IO ()
processFile f =
  do input <- T.readFile f
     case startParsing f input program of
       Left err ->
         do putStrLn (show err)
            exitFailure
       Right (parsed, _) ->
         do let st = TopState None []
            let loc = Loc f (Pos 1 1) (endPos input)
            let (info, res) = runTopElab (mapM_ top parsed) st loc
            dumpInfo info
            case res of
              Left err ->
                do T.putStrLn (printErr input err)
                   exitFailure
              Right _ ->
                exitSuccess

dumpInfo infos =
  traverse (T.putStrLn . dumpLocElabInfo)
    (nub (sortBy (\x y -> compare (getLoc x) (getLoc y)) infos)) *>
  pure ()

repl :: TopState -> IO ()
repl st =
  do putStr "Π> "
     l <- getLine
     if l == ":dump"
       then print st *> repl st
       else do let e = testParser (topLevel <* eof) l
               case e of
                 Left err ->
                   T.putStrLn (printParseErr (T.pack l) err) *>
                   repl st
                 Right parsed@(Located loc _) ->
                   do let (info, res) = runTopElab (top parsed) st loc
                      dumpInfo info
                      case res of
                        Left err ->
                          do T.putStrLn (printErr (T.pack l) err)
                             repl st
                        Right ((), st') ->
                          repl st'

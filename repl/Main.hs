module Main where

import Data.Char
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
            repl (REPLState (TopState None []) Concise)
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

data REPLState = REPLState { topState :: TopState, verbosity :: Verbosity }

data Verbosity = Verbose | Concise

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
            dumpInfo Verbose info
            case res of
              Left err ->
                do T.putStrLn (printErr input err)
                   exitFailure
              Right _ ->
                exitSuccess

dumpInfo v infos =
  do let allInfo = nub (sortBy (\x y -> compare (getLoc x) (getLoc y)) infos)
     case v of
       Verbose -> traverse (T.putStrLn . dumpLocElabInfo) allInfo
       Concise -> traverse T.putStrLn
                    [ i | Just i <- map concise allInfo ]
     pure ()
  where
    concise (Located _ (ExampleOut c)) = Just (printCore c)
    concise i@(Located _ (FoundTODO _ _)) = Just (dumpLocElabInfo i)
    concise _ = Nothing

repl :: REPLState -> IO ()
repl st =
  do putStr "Π> "
     l <- getLine
     case trim l of
       ":dump" ->
         print (topState st) *> repl st
       ":quit" ->
         return ()
       ":verbose" ->
         repl st {verbosity = Verbose}
       ":concise" ->
         repl st {verbosity = Concise}
       ":help" ->
         do putStrLn "This Pie REPL supports anything you can write in a Pie file."
            putStrLn ""
            putStrLn "Additional commands: "
            putStrLn "  :help\tShow this message"
            putStrLn "  :quit\tQuit"
            putStrLn "  :verbose\tTurn on verbose output"
            putStrLn "  :concise\tTurn on concise output (default)"
            repl st
       cmd@(':':_) ->
         do putStrLn $ "Unknown command \"" ++ cmd ++ "\". Use :help for help."
            repl st
       _ ->
         let e = testParser (spacing *> topLevel <* eof) l
         in case e of
              Left err ->
                T.putStrLn (printParseErr (T.pack l) err) *>
                repl st
              Right parsed@(Located loc _) ->
                do let (info, res) = runTopElab (top parsed) (topState st) loc
                   dumpInfo (verbosity st) info
                   case res of
                     Left err ->
                       do T.putStrLn (printErr (T.pack l) err)
                          repl st
                     Right ((), topOut) ->
                       repl st { topState = topOut }

  where trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

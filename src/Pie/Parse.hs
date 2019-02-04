module Pie.Parse where

import Control.Applicative
import Data.Char
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.ICU as ICU

import Pie.Types

data ParseErr = GenericParseErr
              | ExpectedChar Char
              | Expected Text
              | EOF
  deriving Show


data ParserContext =
  ParserContext
    { currentFile :: FilePath
    }

data ParserState =
  ParserState
    { currentInput :: Text
    , currentPos :: Pos
    }

newtype Parser a =
  Parser
    { runParser ::
        ParserContext ->
        ParserState ->
        Either (Positioned ParseErr) (a, ParserState)
    }

instance Functor Parser where
  fmap f (Parser fun) =
    Parser (\ ctx st ->
              case fun ctx st of
                Left err -> Left err
                Right (x, st') -> Right (f x, st'))

instance Applicative Parser where
  pure x = Parser (\_ st -> Right (x, st))
  Parser fun <*> Parser arg =
    Parser (\ ctx st ->
              case fun ctx st of
                Left err -> Left err
                Right (f, st') ->
                  case arg ctx st' of
                    Left err -> Left err
                    Right (x, st'') ->
                      Right (f x, st''))

instance Alternative Parser where
  empty = Parser (\ctx st -> Left (Positioned (currentPos st) GenericParseErr))
  Parser p1 <|> Parser p2 =
    Parser (\ctx st ->
              case p1 ctx st of
                Left _ -> p2 ctx st
                Right ans -> Right ans)

instance Monad Parser where
  return = pure
  Parser act >>= f =
    Parser (\ ctx st ->
              case act ctx st of
                Left err -> Left err
                Right (x, st') ->
                  runParser (f x) ctx st')

failure :: ParseErr -> Parser a
failure e = Parser (\ _ st -> Left (Positioned (currentPos st) e))

get :: Parser ParserState
get = Parser (\ctx st -> Right (st, st))

modify :: (ParserState -> ParserState) -> Parser ()
modify f = Parser (\ctx st -> Right ((), f st))

put :: ParserState -> Parser ()
put = modify . const

getContext :: Parser ParserContext
getContext = Parser (\ctx st -> Right (ctx, st))


forwardLine :: Pos -> Pos
forwardLine (Pos line col) = Pos (line + 1) 1

forwardCol :: Pos -> Pos
forwardCol (Pos line col) = Pos line (col + 1)

char :: Parser Char
char =
  do st <- get
     case T.uncons (currentInput st) of
       Nothing -> failure EOF
       Just (c, more) ->
         do put st { currentInput = more
                   , currentPos =
                     if c == '\n'
                       then forwardLine (currentPos st)
                       else forwardCol (currentPos st)
                   }
            return c

litChar :: Char -> Parser ()
litChar c =
  do c' <- char
     if c == c' then pure () else failure (ExpectedChar c)

located :: Parser a -> Parser (Located a)
located p =
  do file <- currentFile <$> getContext
     startPos <- currentPos <$> get
     res <- p
     endPos <- currentPos <$> get
     return (Located (Loc file startPos endPos) res)

string :: String -> Parser ()
string [] = pure ()
string (c:cs) =
  do c' <- char
     if c /= c'
       then failure (ExpectedChar c)
       else string cs

spanning :: (Char -> Bool) -> Parser Text
spanning p =
  do (matching, rest) <- T.span p . currentInput <$> get
     case T.lines matching of
       [] -> modify (\st -> st { currentInput = rest })
       ls -> modify (\st -> st { currentInput = rest
                               , currentPos = let Pos l c = currentPos st
                                              in Pos (l + length ls) (c + T.length (last ls))
                               })
     return matching

regex :: Text -> [Char] -> Parser Text
regex name rx =
  do input <- currentInput <$> get
     case (ICU.find theRegex input) >>= ICU.group 0  of
       Nothing -> failure (Expected name)
       Just matching ->
         do let rest = T.drop (T.length matching) input
            case T.lines matching of
              [] -> modify (\st -> st { currentInput = rest })
              ls -> modify (\st -> st { currentInput = rest
                                      , currentPos = let Pos l c = currentPos st
                                                     in Pos (l + length ls) (c + T.length (last ls))
                                      })
            return matching
  where
    theRegex = ICU.regex [] (T.pack ('^' : rx))

hashLang :: Parser ()
hashLang = regex (T.pack "language identification") "#lang pie" *> eatSpaces

ident :: Parser Text
ident = regex (T.pack "identifier") "[\\p{Letter}-][\\p{Letter}0-9₀₁₂₃₄₅₆₇₈₉-]*"

varName =
  do x <- Symbol <$> ident
     if x `elem` pieKeywords
       then failure (Expected (T.pack "valid name"))
       else return (Var x)

kw k = regex (T.pack k) k

eatSpaces :: Parser ()
eatSpaces = spanning isSpace *> pure ()

parens :: Parser a -> Parser a
parens p = litChar '(' *> p <* litChar ')'

expr :: Parser Expr
expr = (Expr <$> located expr') <* eatSpaces

expr' :: Parser Expr'
expr' = u <|> nat <|> natLit <|> varName <|> compound
  where
    u = string "U" *> pure U
    nat = string "Nat" *> pure Nat
    tick = Tick . Symbol <$> (litChar '\'' *> ident)
    natLit = do i <- read . T.unpack <$> regex (T.pack "natural number literal") "[0-9]+"
                makeNat i

    compound =
      parens (add1 <|> _)

    add1 = Add1 <$> (kw "add1" *> eatSpaces *> expr)

    makeNat :: Integer -> Parser Expr'
    makeNat i
      | i < 1 = return Zero
      | otherwise = Add1 . Expr <$> located (makeNat (i - 1))

testParser :: Parser a -> String -> Either (Positioned ParseErr) a
testParser (Parser p) input =
  let initSt = ParserState (T.pack input) (Pos 1 1)
      initCtx = ParserContext "<test input>"
  in case p initCtx initSt of
       Left err -> Left err
       Right (x, _) -> Right x

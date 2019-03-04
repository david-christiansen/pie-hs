{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Pie.Parse where

import Control.Applicative
import Data.Char
import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
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
                Left e1 ->
                  case p2 ctx st of
                    Left e2 ->
                      Left (furthest e1 e2)
                    Right ans -> Right ans
                Right ans -> Right ans)
    where
      furthest e1@(Positioned p1 _) e2@(Positioned p2 _) =
        if p1 > p2 then e1 else e2

instance Monad Parser where
  return = pure
  Parser act >>= f =
    Parser (\ ctx st ->
              case act ctx st of
                Left err -> Left err
                Right (x, st') ->
                  runParser (f x) ctx st')

eof :: Parser ()
eof = Parser (\ _ st ->
                if T.null (currentInput st)
                  then Right ((), st)
                  else Left (Positioned (currentPos st) EOF))

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

forwardCols :: Int -> Pos -> Pos
forwardCols n (Pos line col) = Pos line (col + n)



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

rep :: Parser a -> Parser [a]
rep p = ((:) <$> p <*> (rep p)) <|> pure []

rep1 :: Parser a -> Parser (NonEmpty a)
rep1 p = (:|) <$> p <*> rep p

rep_ p = rep p *> pure ()

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

forwardText :: Pos -> Text -> Pos
forwardText (Pos l c) txt =
  case T.split (== '\n') txt of
    [] -> Pos l c
    [line] -> Pos l (c + T.length line)
    lines -> Pos (l + length lines - 1) (1 + T.length (last lines))

spanning :: (Char -> Bool) -> Parser Text
spanning p =
  do (matching, rest) <- T.span p . currentInput <$> get
     modify
       (\st -> st { currentInput = rest
                  , currentPos = forwardText (currentPos st) matching
                  })
     return matching

regex :: Text -> [Char] -> Parser Text
regex name rx =
  do input <- currentInput <$> get
     case (ICU.find theRegex input) >>= ICU.group 0  of
       Nothing -> failure (Expected name)
       Just matching ->
         do let rest = T.drop (T.length matching) input
            modify (\st -> st { currentInput = rest
                              , currentPos = forwardText (currentPos st) matching
                              })
            return matching
  where
    theRegex = ICU.regex [] (T.pack ('^' : rx))

hashLang :: Parser ()
hashLang = regex (T.pack "language identification") "#lang pie" *> spacing


-- | The identifier rules from R6RS Scheme
ident :: Parser Text
ident = regex (T.pack "identifier")
          ("\\A(?:(?:" ++ initial ++ "(?:" ++ subsequent ++ ")*+)|\\+|\\.\\.\\.)")

initial = "[\\p{L}\\p{Lu}\\p{Ll}\\p{Lt}\\p{Lm}\\p{Lo}\\p{Mn}\\p{Nl}\\p{No}\\p{Pd}\\p{Pc}\\p{Po}\\p{Sc}\\p{Sm}\\p{Sk}\\p{So}\\p{Co}!$%&*/:<=>?_~^]"
subsequent = initial ++ "|(?:[0-9₀₁₂₃₄₅₆₇₈₉]|[\\p{Nd}\\p{Mc}\\p{Me}]|\\+|\\.|@)"

token :: Parser a -> Parser (Located a)
token p = located p <* spacing

varName =
  token $
  do x <- Symbol <$> ident
     if x `elem` pieKeywords
       then failure (Expected (T.pack "valid name"))
       else return x

kw k = token $ do x <- ident
                  if T.pack k == x then return () else empty

spacing :: Parser ()
spacing =
  rep_ $
    litChar ' '  <|>
    litChar '\r' <|>
    litChar '\n' <|>
    litChar '\t' <|>
    lineComment  <|>
    exprComment


lineComment :: Parser ()
lineComment = regex (T.pack "line comment") ";[^\n]*\n" *> pure ()

exprComment :: Parser ()
exprComment = ignore (token (string "#;") *> sexpr)
  where
    sexpr = token (ignore (parens (many sexpr)) <|> ignore ident <|> ignore natLit)
    ignore = fmap (const ())

parens :: Parser a -> Parser a
parens p = token (litChar '(') *> p <* token (litChar ')')

parensLoc :: Parser a -> Parser (Located a)
parensLoc p = do Located open _ <- token (litChar '(')
                 res <- p
                 Located close _ <- token (litChar ')')
                 return (Located (spanLocs open close) res)

natLit = do Located loc i <- token (regex (T.pack "natural number literal") "[0-9]+")
            return (Located loc (NatLit (read (T.unpack i))))


pair x y = (x, y)

atLoc :: Parser (Located a) -> b -> Parser (Located b)
atLoc p x = fmap (fmap (const x)) p

expr :: Parser Expr
expr = do Located loc e <- expr'
          return (Expr loc e)

expr' :: Parser (Located (Expr' Loc))
expr' = asum [ tick
             , fmap Var <$> varName
             , u
             , nat
             , triv, sole
             , atom
             , zero, natLit
             , nil
             , vecNil
             , absurd
             , todo
             ] <|> compound
  where
    atomic k v = atLoc (kw k) v
    u = atomic "U" U
    nat = atomic "Nat" Nat
    atom = atomic "Atom" Atom
    zero = atomic "zero" Zero
    triv = atomic "Trivial" Trivial
    sole = atomic "sole" Sole
    nil = atomic "nil" ListNil
    absurd = atomic "Absurd" Absurd
    tick = do Located loc x <- token (litChar '\'' *> ident)  -- TODO separate atom name from var name - atom name has fewer possibilities!
              return (Located loc (Tick (Symbol x)))
    vecNil = atomic "vecnil" VecNil
    todo = atomic "TODO" TODO
    compound =
      parensLoc (asum [ add1, whichNat, iterNat, recNat, indNat
                      , lambda, pi, arrow
                      , the
                      , sigma, pairT , cons , car , cdr
                      , eq, same, replace, trans, cong, symm, indEq
                      , list, listCons, recList, indList
                      , vec, vecCons, vecHead, vecTail, indVec
                      , either, left, right, indEither
                      , indAbsurd
                      ] <|> app)

    add1 = kw "add1" *> (Add1 <$> expr)

    lambda = (kw "lambda" <|> kw "λ") *> (Lambda <$> argList <*> expr)
      where argList = parens (rep1 (do Located loc x <- varName
                                       return (loc, x)))

    pi = (kw "Pi" <|> kw "Π") *> (Pi <$> typedBinders <*> expr)

    arrow = (kw "->" <|> kw "→") *> (Arrow <$> expr <*> rep1 expr)

    typedBinders = parens (rep1 (parens (do Located loc x <- varName
                                            ty <- expr
                                            return (loc, x, ty))))

    sigma = (kw "Sigma" <|> kw "Σ") *> (Sigma <$> typedBinders <*> expr)
    pairT = kw "Pair" *> (Pair <$> expr <*> expr)
    cons = kw "cons" *> (Cons <$> expr <*> expr)
    whichNat = kw "which-Nat" *> (WhichNat <$> expr <*> expr <*> expr)
    iterNat = kw "iter-Nat" *> (IterNat <$> expr <*> expr <*> expr)
    recNat = kw "rec-Nat" *> (RecNat <$> expr <*> expr <*> expr)
    indNat = kw "ind-Nat" *> (IndNat <$> expr <*> expr <*> expr <*> expr)
    car = kw "car" *> (Car <$> expr)
    cdr = kw "cdr" *> (Cdr <$> expr)

    the = kw "the" *> (The <$> expr <*> expr)

    eq = kw "=" *> (Eq <$> expr <*> expr <*> expr)

    same = kw "same" *> (Same <$> expr)

    replace = kw "replace" *> (Replace <$> expr <*> expr <*> expr)

    trans = kw "trans" *> (Trans <$> expr <*> expr)

    cong = kw "cong" *> (Cong <$> expr <*> expr)

    symm = kw "symm" *> (Symm <$> expr)

    indEq = kw "ind-=" *> (IndEq <$> expr <*> expr <*> expr)

    list = kw "List" *> (List <$> expr)

    listCons = kw "::" *> (ListCons <$> expr <*> expr)

    recList = kw "rec-List" *> (RecList <$> expr <*> expr <*> expr)

    indList = kw "ind-List" *> (IndList <$> expr <*> expr <*> expr <*> expr)

    vec = kw "Vec" *> (Vec <$> expr <*> expr)

    vecCons = kw "vec::" *> (VecCons <$> expr <*> expr)

    vecHead = kw "head" *> (VecHead <$> expr)

    vecTail = kw "tail" *> (VecTail <$> expr)

    indVec = kw "ind-Vec" *> (IndVec <$> expr <*> expr <*> expr <*> expr <*> expr)

    either = kw "Either" *> (Either <$> expr <*> expr)

    left = kw "left" *> (EitherLeft <$> expr)

    right = kw "right" *> (EitherRight <$> expr)

    indEither = kw "ind-Either" *> (IndEither <$> expr <*> expr <*> expr <*> expr)

    indAbsurd = kw "ind-Absurd" *> (IndAbsurd <$> expr <*> expr)

    app = App <$> expr <*> rep1 expr


topLevel :: Parser (Located (TopLevel Expr))
topLevel = parensLoc topLevel' <|>
           ((\e@(Expr loc _) -> Located loc (Example e)) <$> expr)

topLevel' = claim <|> define <|> checkSame
  where
    claim = kw "claim" *> (Claim <$> varName <*> expr)
    define = kw "define" *> (Define <$> varName <*> expr)
    checkSame = kw "check-same" *> (CheckSame <$> expr <*> expr <*> expr)

program :: Parser [Located (TopLevel Expr)]
program = hashLang *> rep topLevel <* eof

testParser :: Parser a -> String -> Either (Positioned ParseErr) a
testParser (Parser p) input =
  let initSt = ParserState (T.pack input) (Pos 1 1)
      initCtx = ParserContext "<test input>"
  in case p initCtx initSt of
       Left err -> Left err
       Right (x, _) -> Right x

keepParsing ::
  FilePath ->
  ParserState ->
  Parser a ->
  Either (Positioned ParseErr) (a, ParserState)
keepParsing file st (Parser p) =
  p (ParserContext file) st

startParsing ::
  FilePath ->
  Text ->
  Parser a ->
  Either (Positioned ParseErr) (a, ParserState)
startParsing file input p =
  let initSt = ParserState input (Pos 1 1)
  in keepParsing file initSt p

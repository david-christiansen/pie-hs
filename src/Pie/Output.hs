{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Utilities for displaying output to users
module Pie.Output (
  -- * Pretty-printing Pie
  printCore,
  -- * Displaying error messages
  printParseErr, printErr,
  -- * Displaying output from successful elaboration
  dumpLocElabInfo, printInfo,
  -- * Displaying source locations
  printLoc
  ) where

import Data.List
import Data.List.NonEmpty (NonEmpty(..))
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T

import Pie.Parse (ParseErr(..))
import Pie.Types

data OutputState =
  OutputState { outputLines :: Bwd Text
              , outputLineNum :: Int
              , outputCurrentLine :: Text
              }

initOutputState = OutputState None 0 T.empty

newtype Output a = Output { runOutput :: Int -> OutputState -> (a, OutputState) }

execOutput :: Output () -> Text
execOutput act =
  let st = snd (runOutput act 0 initOutputState)
  in squish (outputLines st :> outputCurrentLine st)
  where
    squish None = T.empty
    squish (None :> line) = line
    squish (lines :> line) =
      squish lines <> T.singleton '\n' <> line

instance Functor Output where
  fmap f (Output g) =
    Output (\i st -> let (x, st') = g i st in (f x, st'))

instance Applicative Output where
  pure x = Output (\_ st -> (x, st))
  Output fun <*> Output arg =
    Output (\i st ->
              let (f, st') = fun i st
                  (x, st'') = arg i st'
              in (f x, st''))

instance Monad Output where
  return = pure
  Output act >>= f =
    Output (\i st ->
              let (x, st') = act i st
              in runOutput (f x) i st')


newline :: Output ()
newline =
  Output (\i st ->
            ((), st { outputLines = outputLines st :> outputCurrentLine st
                    , outputLineNum = 1 + outputLineNum st
                    , outputCurrentLine = T.replicate i (T.singleton ' ')
                    }))

get :: Output OutputState
get = Output (\_ st -> (st, st))

modify :: (OutputState -> OutputState) -> Output ()
modify f = Output (\i st -> ((), f st))

out :: String -> Output ()
out = textOut . T.pack

textOut :: Text -> Output ()
textOut txt = modify (\st -> st { outputCurrentLine = outputCurrentLine st <> txt })

currentIndent :: Output Int
currentIndent = Output (\i st -> (i, st))

indented :: Int -> Output a -> Output a
indented n (Output act) =
  Output (\i st -> act (n + i) st)

indentedHere :: Output a -> Output a
indentedHere act =
  do i <- currentIndent
     n <- T.length . outputCurrentLine <$> get
     indented (n - i) act

remove x [] = []
remove x (y:ys) | x == y = remove x ys
                | otherwise = y : remove x ys

addPi x ty (Pi (dom :| doms) ran) =
  Pi (((), x, ty) :| (dom : doms)) ran
addPi x ty other =
  Pi (((), x, ty) :| []) (Expr () other)

addArrow ty (Arrow dom (ran :| rans)) =
  Arrow ty (dom :| (ran : rans))
addArrow ty other =
  Arrow ty (Expr () other :| [])

addSigma x a (Sigma (a' :| as) d) =
  Sigma (((), x, a) :| (a' : as)) d
addSigma x a other =
  Sigma (((), x, a) :| []) (Expr () other)

addLambda x (Lambda (y :| ys) body) =
  Lambda (((), x) :| (y : ys)) body
addLambda x other = Lambda (((), x) :| []) (Expr () other)

resugar :: Core -> (OutExpr, [Symbol])
resugar (CTick x) = resugar0 (Tick x)
resugar CAtom = resugar0 Atom
resugar CZero = resugar0 (NatLit 0)
resugar (CAdd1 k) =
  case resugar k of
    (Expr () Zero, _) -> (Expr () (NatLit 1), [])
    (Expr () (NatLit n), _) -> (Expr () (NatLit (1 + n)), [])
    (other, free) -> (Expr () (Add1 other), free)
resugar (CWhichNat tgt t base step) = resugar3 WhichNat tgt (CThe t base) step
resugar (CIterNat tgt t base step) = resugar3 IterNat tgt (CThe t base) step
resugar (CRecNat tgt t base step) = resugar3 RecNat tgt (CThe t base) step
resugar (CIndNat tgt mot base step) = resugar4 IndNat tgt mot base step
resugar CNat = resugar0 Nat
resugar (CVar x) = (Expr () (Var x), [x])
resugar (CPi x dom ran) =
  let (dom', domf) = resugar dom
      (Expr () ran', ranf) = resugar ran
  in
    if x `elem` ranf
      then (Expr () (addPi x dom' ran'), domf ++ remove x ranf)
      else (Expr () (addArrow dom' ran'), domf ++ remove x ranf)
resugar (CLambda x body) =
  let (Expr () body', bodyf) = resugar body
  in (Expr () (addLambda x body'), remove x bodyf)
resugar (CApp rator rand) =
  let (rator', ratorf) = resugar rator
      (rand', randf) = resugar rand
  in
    case rator' of
      (Expr () (App rator'' (rand1:|rands))) ->
        (Expr () (App rator' (rator'' :| (rand1:rands))), ratorf ++ randf)
      other ->
        (Expr () (App other (rand' :| [])), ratorf ++ randf)
resugar (CSigma x a d) =
  let (a', af) = resugar a
      (Expr () d', df) = resugar d
  in
    if x `elem` df
      then (Expr () (addSigma x a' d'), af ++ remove x df)
      else (Expr () (Pair a' (Expr () d')), af ++ df)
resugar (CCons a d) = resugar2 Cons a d
resugar (CCar p) = resugar1 Car p
resugar (CCdr p) = resugar1 Cdr p
resugar CTrivial = resugar0 Trivial
resugar CSole = resugar0 Sole
resugar (CEq a from to) = resugar3 Eq a from to
resugar (CSame e) = resugar1 Same e
resugar (CReplace tgt mot base) = resugar3 Replace tgt mot base
resugar (CTrans p1 p2) = resugar2 Trans p1 p2
resugar (CCong p _ fun) = resugar2 Cong p fun
resugar (CSymm e) = resugar1 Symm e
resugar (CIndEq tgt mot base) = resugar3 IndEq tgt mot base
resugar (CList elem) = resugar1 List elem
resugar CListNil = resugar0 ListNil
resugar (CListCons e es) = resugar2 ListCons e es
resugar (CRecList tgt _ base step) = resugar3 RecList tgt base step
resugar (CIndList tgt mot base step) = resugar4 IndList tgt mot base step
resugar (CVec elem len) = resugar2 Vec elem len
resugar (CVecCons e es) = resugar2 VecCons e es
resugar CVecNil = resugar0 VecNil
resugar (CVecHead es) = resugar1 VecHead es
resugar (CVecTail es) = resugar1 VecTail es
resugar (CIndVec len es mot base step) = resugar5 IndVec len es mot base step
resugar (CEither l r) = resugar2 Either l r
resugar (CLeft l) = resugar1 EitherLeft l
resugar (CRight l) = resugar1 EitherRight l
resugar (CIndEither tgt mot l r) = resugar4 IndEither tgt mot l r
resugar CAbsurd = resugar0 Absurd
resugar (CIndAbsurd tgt mot) = resugar2 IndAbsurd tgt mot
resugar CU = resugar0 U
resugar (CThe t e) = resugar2 The t e
resugar (CTODO _ _) = resugar0 TODO

resugar0 f =
  (Expr () f, [])
resugar1 f e =
  let (e', ef) = resugar e
  in (Expr () (f e'), ef)
resugar2 f e1 e2 =
  let (e1', e1f) = resugar e1
      (e2', e2f) = resugar e2
  in (Expr () (f e1' e2'), e1f ++ e2f)
resugar3 f e1 e2 e3 =
  let (e1', e1f) = resugar e1
      (e2', e2f) = resugar e2
      (e3', e3f) = resugar e3
  in (Expr () (f e1' e2' e3'), e1f ++ e2f ++ e3f)
resugar4 f e1 e2 e3 e4 =
  let (e1', e1f) = resugar e1
      (e2', e2f) = resugar e2
      (e3', e3f) = resugar e3
      (e4', e4f) = resugar e4
  in (Expr () (f e1' e2' e3' e4'), e1f ++ e2f ++ e3f ++ e4f)
resugar5 f e1 e2 e3 e4 e5 =
  let (e1', e1f) = resugar e1
      (e2', e2f) = resugar e2
      (e3', e3f) = resugar e3
      (e4', e4f) = resugar e4
      (e5', e5f) = resugar e5
  in (Expr () (f e1' e2' e3' e4' e5'), e1f ++ e2f ++ e3f ++ e4f ++ e5f)

split n xs | n <= 0 = ([], xs)
split n [] = ([], [])
split n (x:xs) =
  let (before, after) = split (n - 1) xs
  in (x : before, after)

parens :: Output a -> Output a
parens act = out "(" *> indentedHere act <* out ")"

hsep :: [Output a] -> Output ()
hsep [] = return ()
hsep [x] = x *> return ()
hsep (x:xs) =
  do before <- outputLineNum <$> get
     x
     after <- outputLineNum <$> get
     if before == after
       then space *> hsep xs
       else newline *> vsep xs

vsep :: [Output a] -> Output ()
vsep [] = return ()
vsep [x] = x *> return ()
vsep (x:xs) = x *> newline *> vsep xs


tiny :: OutExpr -> Bool
tiny (Expr () e) = tiny' e
  where
    tiny' Zero = True
    tiny' (Tick _) = True
    tiny' ListNil = True
    tiny' VecNil = True
    tiny' (NatLit _) = True
    tiny' Atom = True
    tiny' Nat = True
    tiny' U = True
    tiny' (Var _) = True
    tiny' _ = False

elim1 name tgt methods =
  parens $
    if tiny tgt
      then indented 2 $
             do hsep [out name, pp tgt]
                newline
                vsep (map pp methods)
      else do out name
              space
              indentedHere (pp tgt)
              indented 2 $
                do newline
                   vsep (map pp methods)

elim2 name tgt1 tgt2 methods =
  parens $
    if tiny tgt1
      then
        indented 2 $
          do hsep [out name, pp tgt1, pp tgt2]
             newline
             vsep (map pp methods)
      else
        do out name
           space
           indentedHere (do pp tgt1
                            newline
                            pp tgt2)
           indented 2 $
             do newline
                vsep (map pp methods)


space = out " "

form name args =
  let (little, big) = span tiny args
  in parens . indented 1 $
       do out name
          mapM_ (\e -> space *> pp e) little
          mapM_ (\e -> newline *> pp e) big

-- TODO newlines and indentation and such - this is a placeholder
pp :: OutExpr -> Output ()
pp (Expr () e) = pp' e

pp' :: Expr' () -> Output ()
pp' (Tick x) = textOut (T.pack "'" <> symbolName x)
pp' Atom = out "Atom"
pp' Zero = out "zero"
pp' (Add1 n) = form "add1" [n]
pp' (NatLit n) = out (show n)
pp' (WhichNat tgt base step) = elim1 "which-Nat" tgt [base, step]
pp' (IterNat tgt base step) = elim1 "iter-Nat" tgt [base, step]
pp' (RecNat tgt base step) = elim1 "rec-Nat" tgt [base, step]
pp' (IndNat tgt mot base step) =
  elim1 "ind-Nat" tgt [mot, base, step]
pp' Nat = out "Nat"
pp' (Var x) = textOut (symbolName x)
pp' (Arrow dom (ran:|rans)) =
  let (args, ret) = splitArgs (dom :| (ran : rans))
  in parens $
       do out "→"
          space
          indentedHere $
            if all tiny args
              then hsep (map pp args)
              else vsep (map pp args)
          indented 1 (newline *> pp ret)
  where
    splitArgs (t :| []) = ([], t)
    splitArgs (t:|(x:xs)) =
      let (args', ret) = splitArgs (x :| xs)
      in (t : args', ret)
pp' (Pi args body) =
  parens (out "Π " *> parens (vsep (binds args) *>
          indented 1 (newline *> pp body)))
  where binds (b :| []) = [bind b]
        binds (b :| (b':bs)) = bind b : binds (b' :| bs)
        bind (_, x, e) = parens (textOut (symbolName x) *> out " " *> pp e)
pp' (Lambda xs body) =
  parens . indented 1 $
    do out "λ"
       space
       parens (args xs)
       newline
       pp body
  where
    args ((_, x) :| []) =
      textOut (symbolName x)
    args ((_, x) :| (y:xs)) =
      textOut (symbolName x) *> space *> args (y :| xs)
pp' (App rator (rand1 :| rands)) =
  let (small, big) = span tiny (rand1 : rands)
  in parens . indented 1 $
       if tiny rator
         then hsep (map pp (rator : small)) *> newline *> vsep (map pp big)
         else pp rator *> newline *> vsep (map pp (rand1 : rands))
pp' (Sigma args body) =
  parens (out "Σ " *> parens (indentedHere (vsep (binds args)) *>
          indented 2 (newline *> pp body)))
  where binds (b :| []) = [bind b]
        binds (b :| (b':bs)) = bind b : binds (b' :| bs)
        bind (_, x, e) = parens (textOut (symbolName x) *> out " " *> pp e)
pp' (Pair a d) = form "Pair" [a, d]
pp' (Cons a d)
  | tiny a && tiny d =
    parens (hsep [out "cons", pp a, pp d])
  | otherwise =
    parens (do out "cons"
               space
               pp a
               newline
               pp d)
pp' (Car p) = form "car" [p]
pp' (Cdr p) = form "cdr" [p]
pp' Trivial = out "Trivial"
pp' Sole = out "sole"
pp' (Eq t from to)
  | all tiny [t, from, to] =
    parens (hsep [out "=", pp t, pp from, pp to])
  | otherwise =
    parens (vsep [do out "=" *> space *> pp t, pp from, pp to])
pp' (Same e) = form "same" [e]
pp' (Replace tgt mot base) =
  elim1 "replace" tgt [mot, base]
pp' (Trans p1 p2) = form "trans" [p1, p2]
pp' (Cong p fun) = form "cong" [p, fun]
pp' (Symm e) = form "symm" [e]
pp' (IndEq tgt mot base) = elim1 "ind-=" tgt [mot, base]
pp' (List elem) = form "List" [elem]
pp' ListNil = out "nil"
pp' (ListCons e es) = form "::" [e, es]
pp' (RecList tgt base step) = elim1 "rec-List" tgt [base, step]
pp' (IndList tgt mot base step) = elim1 "ind-List" tgt [mot, base, step]
pp' (Vec elem len) = form "Vec" [elem, len]
pp' VecNil = out "vecnil"
pp' (VecCons e es) = form "vec::" [e, es]
pp' (VecHead es) = form "head" [es]
pp' (VecTail es) = form "tail" [es]
pp' (IndVec len tgt mot base step) = elim2 "ind-Vec" len tgt [mot, base, step]
pp' (Either l r) = form "Either" [l, r]
pp' (EitherLeft l) = form "left" [l]
pp' (EitherRight r) = form "right" [r]
pp' (IndEither tgt mot l r) = elim1 "ind-Either" tgt [mot, l, r]
pp' Absurd = out "Absurd"
pp' (IndAbsurd tgt mot) = elim1 "ind-Absurd" tgt [mot]
pp' U = out "U"
pp' (The t e) =
  parens . indented 1 $
    do out "the"
       space
       indentedHere (pp t)
       newline
       pp e
pp' TODO = out "TODO"

spaced ss = mconcat (intersperse (T.pack " ") ss)

indentTextBlock i txt =
  let lines = T.lines txt
  in case lines of
    [] -> T.empty
    [l] -> l
    _ -> T.singleton '\n' <>
         T.unlines [ T.replicate i (T.singleton ' ') <> line
                   | line <- lines
                   ]

-- | Pretty-print a core expression, after resugaring it
printCore :: Core -> Text
printCore c = execOutput (pp (fst (resugar c)))

-- | Display a particular piece of elaboration information.
printInfo :: ElabInfo -> Text
printInfo (ExprHasType c) =
  let expr = fst (resugar c)
      str = execOutput (pp expr)
  in T.pack "Has type " <>
     if tiny expr then str else indentTextBlock 2 str
printInfo ExprIsType = T.pack "A type"
printInfo (ExprWillHaveType c) =
  T.pack "Will have type " <> execOutput (pp (fst (resugar c)))
printInfo (ClaimAt loc) =
  T.pack "Claim from " <> printLoc loc
printInfo (BoundAt loc) =
  T.pack "Bound at " <> printLoc loc
printInfo (ExampleOut c) =
  let expr = fst (resugar c)
      norm = execOutput (pp expr)
  in T.pack "Example's normal form is " <>
     if tiny expr
       then norm
       else indentTextBlock 2 norm
printInfo (FoundTODO ctx ty) =
  let ctx' = printTODOCtx ctx
      ty'  = execOutput (pp (fst (resugar ty)))
      line = T.replicate (2 + maxLineLength (ctx' <> nl <> ty')) (T.pack "-")
  in T.pack "Found TODO:" <> indent ctx' <> line <> nl <> indent ty'

  where
    nl :: Text
    nl = T.singleton '\n'
    indent :: Text -> Text
    indent txt = T.unlines [T.pack " " <> line | line <- T.lines txt]
    maxLineLength :: Text -> Int
    maxLineLength txt =
      foldr max 0 [T.length line | line <- T.lines txt]

printTODOCtx :: Bwd (Symbol, Maybe Loc, Core) -> Text
printTODOCtx ctx =
  let nameWidth = foldr max 0 (map T.length (getNames ctx))
  in T.pack "\n" <> T.unlines [showLine nameWidth x t | (x, _, t) <- toList ctx []]
  where
    getNames None = []
    getNames (c :> (x, _, _)) = symbolName x : getNames c

    toList None ys = ys
    toList (xs :> x) ys = toList xs (x:ys)

    showLine w x t =
      padTo w (symbolName x) <> T.pack " : " <> execOutput (pp (fst (resugar t)))

    padTo w txt = T.replicate (w - T.length txt) (T.singleton ' ') <> txt

-- | Display elaboration information.
dumpLocElabInfo :: Located ElabInfo -> Text
dumpLocElabInfo (Located loc info) =
  printLoc loc <> T.pack ": " <> printInfo info

-- | Display an elaboration error (that is, a type error) with respect
-- to the source document from which it arose.
--
-- The source document is used to construct a highlighted view of the
-- source location.
printErr :: Text -> ElabErr -> Text
printErr input (ElabErr (Located loc msg)) =
    printLoc loc <> T.pack ": " <>
    highlightLoc input loc <>
    mconcat (intersperse (T.singleton ' ') [showPart part | part <- msg])
  where
    showPart (MText txt) =
      txt
    showPart (MVal c) =
      let e = fst (resugar c)
          out = execOutput (pp e)
      in if tiny e
           then out
           else indentTextBlock 2 out

highlightLoc :: Text -> Loc -> Text
highlightLoc input (Loc fn (Pos l1 c1) (Pos l2 c2)) =
  if l1 == l2
    then
      case findLine l1 input of
        Nothing -> T.empty
        Just line ->
          T.pack "\n  " <> line <>
          T.pack "\n  " <> spaces c1 <> caret <> dashes (c2 - c1 - 1) <> caret <> nl
    else
      case pair <$> findLine l1 input <*> findLine l2 input of
        Nothing -> T.empty
        Just (line1, line2) ->
          T.pack "\n  " <> spaces (T.length label1 + c1) <> vee <> dashes (max (T.length line1) (T.length line2) - 2) <>
          T.pack "\n  " <> label1 <> line1 <>
          T.pack (if l2 - l1 == 1 then "" else "\n" ++ replicate (T.length label1) ' ' ++  "  ...") <>
          T.pack "\n  " <> label2 <> line2 <>
          T.pack "\n  " <> spaces (T.length label2 + 1) <> dashes (c2 - 1) <> caret <> nl
  where
    (label1, label2) =
      let l1str = show l1
          l2str = show l2
      in
        (T.pack (replicate (length l1str - length l2str) ' ' ++ l1str ++ ": "),
         T.pack (replicate (length l2str - length l1str) ' ' ++ l2str ++ ": "))
    pair x y = (x, y)
    caret = T.pack "^"
    vee = T.pack "v"
    nl = T.pack "\n"
    spaces n = T.replicate (n - 1) (T.pack " ")
    dashes n = T.replicate (n - 1) (T.pack "-")
    lineID l = T.pack fn

highlightPos :: Text -> Pos -> Text
highlightPos input (Pos l c) =
  case findLine l input of
    Nothing -> T.empty
    Just line ->
      T.pack "\n  " <> line <>
      T.pack "\n  " <> T.replicate (c - 1) (T.pack "-") <> T.pack "^\n"

findLine :: Int -> Text -> Maybe Text
findLine n input = find' n (T.lines input)
  where
    find' n (l:ls)
      | n <= 1 = Just l
      | otherwise = find' (n - 1) ls
    find' _ [] = Nothing

-- | Display a parser error with respect to the input from which it arose.
--
-- The input is used to produce a highlighted version with a pointer
-- to the specific location.
printParseErr :: Text -> Positioned ParseErr -> Text
printParseErr input (Positioned pos@(Pos l c) e) =
  mconcat
  [ T.pack ("Parse error at " ++ show l ++ ":" ++ show c ++ ":")
  , highlightPos input pos
  , case e of
      GenericParseErr -> T.empty
      Expected cs ds ->
        T.pack "Expected " <>
        (case cs of
           [] -> T.empty
           [c] -> T.pack ("the character " ++ show c)
           _ -> T.pack ("one of " ++ concat (intersperse ", " (show <$> cs)))) <>
        (case (cs, ds) of
           ((_:_), (_:_)) -> T.pack " or "
           _ -> mempty) <>
        (case ds of
           [] -> mempty
           [d] -> d
           _ -> T.intercalate (T.pack " or ") ds)
      EOF -> T.pack "end of input"
  ]

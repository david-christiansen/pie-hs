module Pie.Output where

import Data.List
import Data.List.NonEmpty (NonEmpty(..))
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T

import Pie.Types

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
resugar CZero = resugar0 Zero
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

-- TODO newlines and indentation and such - this is a placeholder
pp :: OutExpr -> Text
pp (Expr () e) = pp' e

pp' (Tick x) = T.pack "'" <> symbolName x
pp' Atom = T.pack "Atom"
pp' Zero = T.pack "zero"
pp' (Add1 n) = T.pack "(add1 " <> pp n <> T.pack ")"
pp' (NatLit n) = T.pack (show n)
pp' (WhichNat tgt base step) = list "which-Nat" [tgt, base, step]
pp' (IterNat tgt base step) = list "iter-Nat" [tgt, base, step]
pp' (RecNat tgt base step) = list "rec-Nat" [tgt, base, step]
pp' (IndNat tgt mot base step) = T.pack "(ind-Nat " <> spaced (map pp [tgt, mot, base, step]) <> T.pack ")"
pp' Nat = T.pack "Nat"
pp' (Var x) = symbolName x
pp' (Arrow dom (ran:|rans)) = T.pack "(→ " <> pp dom <> T.pack " " <> spaced (map pp (ran:rans)) <> T.pack ")"
pp' (Pi args body) = T.pack "(Π (" <> binds args <> T.pack ") " <> pp body <> T.pack ")"
  where binds (b :| []) = bind b
        binds (b :| (b':bs)) = bind b <> T.pack " " <> binds (b' :| bs)
        bind (_, x, e) = T.pack "(" <> symbolName x <> T.pack " " <> pp e <> T.pack ")"
pp' (Lambda xs body) = T.pack "(λ (" <> args xs <> T.pack ") " <> pp body <> T.pack ")"
  where args ((_, x) :| []) = symbolName x
        args ((_, x) :| (y:xs)) = symbolName x <> T.pack " " <> args (y:|xs)
pp' (App rator (rand1 :| rands)) =
  T.pack "(" <> pp rator <> T.pack " " <> pp rand1 <> more rands <> T.pack ")"
  where
    more [] = T.empty
    more [x] = pp x
    more es@(_:_) = spaced (map pp es)
pp' (Sigma args body) = T.pack "(Σ (" <> binds args <> T.pack ") " <> pp body <> T.pack ")"
  where binds (b :| []) = bind b
        binds (b :| (b':bs)) = bind b <> T.pack " " <> binds (b' :| bs)
        bind (_, x, e) = T.pack "(" <> symbolName x <> T.pack " " <> pp e <> T.pack ")"
pp' (Pair a d) = T.pack "(Pair " <> pp a <> T.pack " " <> pp d <> T.pack ")"
pp' (Cons a d) = T.pack "(cons " <> pp a <> T.pack " " <> pp d <> T.pack ")"
pp' (Car p) = T.pack "(car " <> pp p <> T.pack ")"
pp' (Cdr p) = T.pack "(cdr " <> pp p <> T.pack ")"
pp' Trivial = T.pack "Trivial"
pp' Sole = T.pack "sole"
pp' (Eq t from to) = list "=" [t, from, to]
pp' (Same e) = list "same" [e]
pp' (Replace tgt mot base) = list "replace" [tgt, mot, base]
pp' (Trans p1 p2) = list "trans" [p1, p2]
pp' (Cong p fun) = list "cong" [p, fun]
pp' (Symm e) = list "symm" [e]
pp' (IndEq tgt mot base) = list "ind-=" [tgt, mot, base]
pp' (List elem) = list "List" [elem]
pp' ListNil = T.pack "nil"
pp' (ListCons e es) = list "::" [e, es]
pp' (RecList tgt base step) = list "rec-List" [tgt, base, step]
pp' (IndList tgt mot base step) = list "ind-List" [tgt, mot, base, step]
pp' (Vec elem len) = list "Vec" [elem, len]
pp' VecNil = T.pack "vecnil"
pp' (VecCons e es) = list "vec::" [e, es]
pp' (VecHead es) = list "head" [es]
pp' (VecTail es) = list "tail" [es]
pp' (IndVec len tgt mot base step) = list "ind-Vec" [len, tgt, mot, base, step]
pp' (Either l r) = list "Either" [l, r]
pp' (EitherLeft l) = list "left" [l]
pp' (EitherRight r) = list "right" [r]
pp' (IndEither tgt mot l r) = list "ind-Either" [tgt, mot, l, r]
pp' Absurd = T.pack "Absurd"
pp' (IndAbsurd tgt mot) = list "ind-Absurd" [tgt, mot]
pp' U = T.pack "U"
pp' (The t e) = T.pack "(the " <> pp t <> T.pack " " <> pp e <> T.pack ")"

spaced ss = mconcat (intersperse (T.pack " ") ss)

list name args = T.pack "(" <> T.pack name <> T.pack " " <> spaced (map pp args) <> T.pack ")"

printInfo :: ElabInfo -> Text
printInfo (ExprHasType c) =
  T.pack "Has type " <> pp (fst (resugar c))
printInfo ExprIsType = T.pack "A type"
printInfo (ExprWillHaveType c) =
  T.pack "Will have type " <> pp (fst (resugar c))
printInfo (ClaimAt loc) =
  T.pack "Claim from " <> printLoc loc
printInfo (BoundAt loc) =
  T.pack "Bound at " <> printLoc loc
printInfo (ExampleOut c) =
  pp (fst (resugar c))

dumpLocElabInfo :: Located ElabInfo -> Text
dumpLocElabInfo (Located loc info) =
  printLoc loc <> T.pack ": " <> printInfo info

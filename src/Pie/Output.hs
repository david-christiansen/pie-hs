module Pie.Output where

import Data.List
import Data.List.NonEmpty (NonEmpty(..))
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T

import Pie.Types

resugar :: Core -> OutExpr
resugar (CTick x) = Expr () (Tick x)
resugar CAtom = Expr () Atom
resugar CZero = Expr () Zero
resugar (CAdd1 k) =
  case resugar k of
    Expr () Zero -> Expr () (NatLit 1)
    Expr () (NatLit n) -> Expr () (NatLit (1 + n))
    other -> Expr () (Add1 other)
resugar (CIndNat tgt mot base step) =
  Expr () (IndNat (resugar tgt) (resugar mot) (resugar base) (resugar step))
resugar CNat = Expr () Nat
resugar (CVar x) = Expr () (Var x)
resugar (CPi x dom ran) = Expr () (Pi (((), x, resugar dom) :| []) (resugar ran)) -- TODO collapse
resugar (CLambda x body) = Expr () (Lambda (((), x) :| []) (resugar body))
resugar (CApp rator rand) = Expr () (App (resugar rator) (resugar rand :| []))
resugar (CSigma x a d) = Expr () (Sigma (((), x, (resugar a)) :| []) (resugar d))
resugar (CCons a d) = Expr () (Cons (resugar a) (resugar d))
resugar (CCar p) = Expr () (Car (resugar p))
resugar (CCdr p) = Expr () (Cdr (resugar p))
resugar CTrivial = Expr () Trivial
resugar CSole = Expr () Sole
resugar (CEq a from to) = Expr () (Eq (resugar a) (resugar from) (resugar to))
resugar (CSame e) = Expr () (Same (resugar e))
resugar (CReplace tgt mot base) =
  Expr () (Replace (resugar tgt) (resugar mot) (resugar base))
resugar (CTrans p1 p2) = Expr () (Trans (resugar p1) (resugar p2))
resugar (CCong p _ fun) = Expr () (Cong (resugar p) (resugar fun))
resugar (CSymm e) = Expr () (Symm (resugar e))
resugar (CIndEq tgt mot base) = Expr () (IndEq (resugar tgt) (resugar mot) (resugar base))
resugar (CVec elem len) = Expr () (Vec (resugar elem) (resugar len))
resugar (CVecCons e es) = Expr () (VecCons (resugar e) (resugar es))
resugar CVecNil = Expr () VecNil
resugar (CVecHead es) = Expr () (VecHead (resugar es))
resugar (CVecTail es) = Expr () (VecTail (resugar es))
resugar (CIndVec len es mot base step) =
  Expr () (IndVec (resugar len) (resugar es) (resugar mot) (resugar base) (resugar step))
resugar CU = Expr () U
resugar (CThe t e) = Expr () (The (resugar t) (resugar e))

-- TODO newlines and indentation and such - this is a placeholder
pp :: OutExpr -> Text
pp (Expr () e) = pp' e

pp' (Tick x) = T.pack "'" <> symbolName x
pp' Atom = T.pack "Atom"
pp' Zero = T.pack "zero"
pp' (Add1 n) = T.pack "(add1 " <> pp n <> T.pack ")"
pp' (NatLit n) = T.pack (show n)
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
pp' (Vec elem len) = list "Vec" [elem, len]
pp' VecNil = T.pack "vecnil"
pp' (VecCons e es) = list "vec::" [e, es]
pp' (VecHead es) = list "head" [es]
pp' (VecTail es) = list "tail" [es]
pp' (IndVec len tgt mot base step) = list "ind-Vec" [len, tgt, mot, base, step]
pp' U = T.pack "U"
pp' (The t e) = T.pack "(the " <> pp t <> T.pack " " <> pp e <> T.pack ")"

spaced ss = mconcat (intersperse (T.pack " ") ss)

list name args = T.pack "(" <> T.pack name <> T.pack " " <> spaced (map pp args) <> T.pack ")"

printInfo :: ElabInfo -> Text
printInfo (ExprHasType c) =
  T.pack "Has type " <> pp (resugar c)
printInfo ExprIsType = T.pack "A type"
printInfo (ExprWillHaveType c) =
  T.pack "Will have type " <> pp (resugar c)
printInfo (ClaimAt loc) =
  T.pack "Claim from " <> printLoc loc
printInfo (BoundAt loc) =
  T.pack "Bound at " <> printLoc loc
printInfo (ExampleOut c) =
  pp (resugar c)

dumpLocElabInfo :: Located ElabInfo -> Text
dumpLocElabInfo (Located loc info) =
  printLoc loc <> T.pack ": " <> printInfo info

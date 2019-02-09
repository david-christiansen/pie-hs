module Pie.Output where

import Data.List
import Data.List.NonEmpty (NonEmpty(..))
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T

import Pie.Types

resugar :: Core -> OutExpr
resugar (CTick x) = OutExpr (Tick x)
resugar CAtom = OutExpr Atom
resugar CZero = OutExpr Zero
resugar (CAdd1 k) = OutExpr (Add1 (resugar k))
resugar (CIndNat tgt mot base step) =
  OutExpr (IndNat (resugar tgt) (resugar mot) (resugar base) (resugar step))
resugar CNat = OutExpr Nat
resugar (CVar x) = OutExpr (Var x)
resugar (CPi x dom ran) = OutExpr (Pi ((x, resugar dom) :| []) (resugar ran)) -- TODO collapse
resugar (CLambda x body) = OutExpr (Lambda (x :| []) (resugar body))
resugar (CApp rator rand) = OutExpr (App (resugar rator) (resugar rand) [])
resugar (CSigma x a d) = OutExpr (Sigma ((x, (resugar a)) :| []) (resugar d))
resugar (CCons a d) = OutExpr (Cons (resugar a) (resugar d))
resugar (CCar p) = OutExpr (Car (resugar p))
resugar (CCdr p) = OutExpr (Cdr (resugar p))
resugar CTrivial = OutExpr Trivial
resugar CSole = OutExpr Sole
resugar (CEq a from to) = OutExpr (Eq (resugar a) (resugar from) (resugar to))
resugar (CSame e) = OutExpr (Same (resugar e))
resugar (CReplace tgt mot base) =
  OutExpr (Replace (resugar tgt) (resugar mot) (resugar base))
resugar (CTrans p1 p2) = OutExpr (Trans (resugar p1) (resugar p2))
resugar (CCong p _ fun) = OutExpr (Cong (resugar p) (resugar fun))
resugar (CSymm e) = OutExpr (Symm (resugar e))
resugar (CIndEq tgt mot base) = OutExpr (IndEq (resugar tgt) (resugar mot) (resugar base))
resugar CU = OutExpr U
resugar (CThe t e) = OutExpr (The (resugar t) (resugar e))

-- TODO newlines and indentation and such - this is a placeholder
pp :: OutExpr -> Text
pp (OutExpr e) = pp' e

pp' (Tick x) = T.pack "'" <> symbolName x
pp' Atom = T.pack "Atom"
pp' Zero = T.pack "zero"
pp' (Add1 n) = T.pack "(add1 " <> pp n <> T.pack ")"
pp' (IndNat tgt mot base step) = T.pack "(ind-Nat " <> spaced (map pp [tgt, mot, base, step]) <> T.pack ")"
pp' Nat = T.pack "Nat"
pp' (Var x) = symbolName x
pp' (Arrow dom (ran:|rans)) = T.pack "(→ " <> pp dom <> T.pack " " <> spaced (map pp (ran:rans)) <> T.pack ")"
pp' (Pi args body) = T.pack "(Π (" <> binds args <> T.pack ") " <> pp body <> T.pack ")"
  where binds (b :| []) = bind b
        binds (b :| (b':bs)) = bind b <> T.pack " " <> binds (b' :| bs)
        bind (x, e) = T.pack "(" <> symbolName x <> T.pack " " <> pp e <> T.pack ")"
pp' (Lambda xs body) = T.pack "(λ (" <> args xs <> T.pack ") " <> pp body <> T.pack ")"
  where args (x :| []) = symbolName x
        args (x :| (y:xs)) = symbolName x <> T.pack " " <> args (y:|xs)
pp' (App rator rand1 rands) =
  T.pack "(" <> pp rator <> T.pack " " <> pp rand1 <> more rands <> T.pack ")"
  where
    more [] = T.empty
    more [x] = pp x
    more es@(_:_) = spaced (map pp es)
pp' (Sigma args body) = T.pack "(Σ (" <> binds args <> T.pack ") " <> pp body <> T.pack ")"
  where binds (b :| []) = bind b
        binds (b :| (b':bs)) = bind b <> T.pack " " <> binds (b' :| bs)
        bind (x, e) = T.pack "(" <> symbolName x <> T.pack " " <> pp e <> T.pack ")"
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
pp' U = T.pack "U"
pp' (The t e) = T.pack "(the " <> pp t <> T.pack " " <> pp e <> T.pack ")"

spaced ss = mconcat (intersperse (T.pack " ") ss)

list name args = T.pack "(" <> T.pack name <> T.pack " " <> spaced (map pp args) <> T.pack ")"

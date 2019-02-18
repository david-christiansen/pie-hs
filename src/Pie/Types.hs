module Pie.Types where

import Data.List.NonEmpty (NonEmpty)
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T

import Pie.Panic

data Bwd a = None | Bwd a :> a
  deriving (Eq, Ord, Show)

instance Functor Bwd where
  fmap f None = None
  fmap f (xs :> x) = fmap f xs :> f x



newtype Symbol = Symbol { symbolName :: Text }
  deriving (Eq, Ord, Show)

sym :: String -> Symbol
sym = Symbol . T.pack

pieKeywords :: [Symbol]
pieKeywords =
  map (Symbol . T.pack)
  [ "U",
    "Nat", "zero", "add1", "which-Nat", "iter-Nat", "rec-Nat", "ind-Nat",
    "->", "→", "Π", "λ", "Pi", "lambda",
    "quote", "Atom",
    "car", "cdr", "cons", "Σ", "Sigma", "Pair",
    "Trivial", "sole",
    "List", "::", "nil", "rec-List", "ind-List",
    "Absurd", "ind-Absurd",
    "=", "same", "replace", "trans", "cong", "symm", "ind-=",
    "Vec", "vecnil ","vec::", "head", "tail", "ind-Vec",
    "Either", "left", "right", "ind-Either",
    "TODO", "the"]

data Pos = Pos { posLine :: Int, posCol :: Int }
  deriving (Eq, Show)

instance Ord Pos where
  compare (Pos l1 c1) (Pos l2 c2) =
    compare l1 l2 <> compare c1 c2

data Positioned a = Positioned Pos a
  deriving (Eq, Show)

printPos :: Pos -> Text
printPos pos =
  T.pack (show (posLine pos)) <>
  T.pack "." <>
  T.pack (show (posCol pos))

data Loc = Loc { locSource :: FilePath
               , locStart :: Pos
               , locEnd :: Pos
               }
  deriving (Eq, Show)

instance Ord Loc where
  compare (Loc src1 s1 e1) (Loc src2 s2 e2) =
    if src1 /= src2
      then panic ("Tried to compare locations from different souce files: " ++
                  src1 ++ " and " ++ src2)
      else compare s1 s2 <> compare e1 e2

printLoc :: Loc -> Text
printLoc (Loc source start end) =
  T.pack (source ++ ":") <>
  printPos start <>
  T.pack "-" <>
  printPos end


-- | Invariants: non-overlapping regions where the first argument ends
-- before the second starts in same file
spanLocs :: Loc -> Loc -> Loc
spanLocs (Loc src p1 _) (Loc _ _ p2) = Loc src p1 p2

data Located a = Located Loc a
  deriving (Eq, Show)

instance Functor Located where
  fmap f (Located loc x) = Located loc (f x)

getLoc :: Located a -> Loc
getLoc (Located loc _) = loc

unLocate :: Located a -> a
unLocate (Located _ x) = x

data LocatedExpr loc = Expr loc (Expr' loc)
  deriving (Eq, Show)

type Expr = LocatedExpr Loc
type OutExpr = LocatedExpr ()


data Expr' loc = Tick Symbol
               | Atom
               | Zero
               | Add1 (LocatedExpr loc)
               | IndNat (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | Nat
               | Var Symbol
               | Arrow (LocatedExpr loc) (NonEmpty (LocatedExpr loc))
               | Pi (NonEmpty (loc, Symbol, (LocatedExpr loc))) (LocatedExpr loc)
               | Lambda (NonEmpty (loc, Symbol)) (LocatedExpr loc)
               | App (LocatedExpr loc) (NonEmpty (LocatedExpr loc))
               | Sigma (NonEmpty (loc, Symbol, (LocatedExpr loc))) (LocatedExpr loc)
               | Pair (LocatedExpr loc) (LocatedExpr loc)
               | Cons (LocatedExpr loc) (LocatedExpr loc)
               | Car (LocatedExpr loc)
               | Cdr (LocatedExpr loc)
               | Trivial
               | Sole
               | Eq (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | Same (LocatedExpr loc)
               | Replace (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | Trans (LocatedExpr loc) (LocatedExpr loc)
               | Cong (LocatedExpr loc) (LocatedExpr loc)
               | Symm (LocatedExpr loc)
               | IndEq (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | Vec (LocatedExpr loc) (LocatedExpr loc)
               | VecNil
               | VecCons (LocatedExpr loc) (LocatedExpr loc)
               | VecHead (LocatedExpr loc)
               | VecTail (LocatedExpr loc)
               | IndVec (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | U
               | The (LocatedExpr loc) (LocatedExpr loc)
  deriving (Eq, Show)

data Core = CTick Symbol
          | CAtom
          | CZero
          | CAdd1 Core
          | CIndNat Core Core Core Core
          | CNat
          | CVar Symbol
          | CPi Symbol Core Core
          | CLambda Symbol Core
          | CApp Core Core
          | CSigma Symbol Core Core
          | CCons Core Core
          | CCar Core
          | CCdr Core
          | CTrivial
          | CSole
          | CEq Core Core Core
          | CSame Core
          | CReplace Core Core Core
          | CTrans Core Core
          | CCong Core Core Core
          | CSymm Core
          | CIndEq Core Core Core
          | CVec Core Core
          | CVecNil
          | CVecCons Core Core
          | CVecHead Core
          | CVecTail Core
          | CIndVec Core Core Core Core Core
          | CU
          | CThe Core Core
  deriving Show

data Value = VTick Symbol
           | VAtom
           | VNat
           | VZero
           | VAdd1 Value
           | VPi Symbol Value (Closure Value)
           | VLambda Symbol (Closure Value)
           | VSigma Symbol Value (Closure Value)
           | VCons Value Value
           | VTrivial
           | VSole
           | VEq Value Value Value
           | VSame Value
           | VVec Value Value
           | VVecCons Value Value
           | VVecNil
           | VU
           | VNeu Value Neutral
  deriving Show

data Neutral = NVar Symbol
             | NIndNat Neutral Normal Normal Normal
             | NApp Neutral Normal
             | NCar Neutral
             | NCdr Neutral
             | NReplace Neutral Normal Normal
             | NTrans1 Neutral Normal
             | NTrans2 Normal Neutral
             | NTrans12 Neutral Neutral
             | NCong Neutral Normal
             | NSymm Neutral
             | NIndEq Neutral Normal Normal
             | NHead Neutral
             | NTail Neutral
             | NIndVec1 Neutral Normal Normal Normal Normal
             | NIndVec2 Normal Neutral Normal Normal Normal
             | NIndVec12 Neutral Neutral Normal Normal Normal
  deriving Show

data Normal = NThe { normType :: Value, normVal :: Value }
  deriving Show

data Closure a = Closure (Env a) Core
  deriving Show

type Env a = Bwd (Symbol, a)



data MessagePart a = MText Text | MVal a
  deriving Show

data ElabInfo = ExprHasType Core
              | ExprIsType
              | ExprWillHaveType Core -- ^ TODOs


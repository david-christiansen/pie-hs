{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

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
  deriving (Eq, Ord)

instance Show Symbol where
  showsPrec p (Symbol x) =
    showParen (p > 10) (showString ("Symbol \"" ++  T.unpack x ++ "\""))

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
    "Vec", "vecnil","vec::", "head", "tail", "ind-Vec",
    "Either", "left", "right", "ind-Either",
    "TODO", "the"]

data Pos = Pos { posLine :: Int, posCol :: Int }
  deriving (Eq)

instance Show Pos where
  showsPrec p (Pos line col) =
    showParen (p > 10) (showString "Pos " . shows line . showString " " . shows col)

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
  deriving (Eq)

instance Show Loc where
  showsPrec p (Loc src start end) =
    showParen (p > 10) (showString "Loc " . showString (show src) . showString " " . showsPrec 11 start . showString " " . showsPrec 11 end)

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


data Expr' loc = The (LocatedExpr loc) (LocatedExpr loc)
               | Var Symbol
               | Atom
               | Tick Symbol
               | Pair (LocatedExpr loc) (LocatedExpr loc)
               | Sigma (NonEmpty (loc, Symbol, (LocatedExpr loc))) (LocatedExpr loc)
               | Cons (LocatedExpr loc) (LocatedExpr loc)
               | Car (LocatedExpr loc)
               | Cdr (LocatedExpr loc)
               | Arrow (LocatedExpr loc) (NonEmpty (LocatedExpr loc))
               | Pi (NonEmpty (loc, Symbol, (LocatedExpr loc))) (LocatedExpr loc)
               | Lambda (NonEmpty (loc, Symbol)) (LocatedExpr loc)
               | App (LocatedExpr loc) (NonEmpty (LocatedExpr loc))
               | Nat
               | Zero
               | Add1 (LocatedExpr loc)
               | NatLit Integer
               | WhichNat (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | IterNat (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | RecNat (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | IndNat (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | List (LocatedExpr loc)
               | ListNil
               | ListCons (LocatedExpr loc) (LocatedExpr loc)
               | RecList (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | IndList (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | Vec (LocatedExpr loc) (LocatedExpr loc)
               | VecNil
               | VecCons (LocatedExpr loc) (LocatedExpr loc)
               | VecHead (LocatedExpr loc)
               | VecTail (LocatedExpr loc)
               | IndVec (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | Eq (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | Same (LocatedExpr loc)
               | Symm (LocatedExpr loc)
               | Cong (LocatedExpr loc) (LocatedExpr loc)
               | Replace (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | Trans (LocatedExpr loc) (LocatedExpr loc)
               | IndEq (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | Either (LocatedExpr loc) (LocatedExpr loc)
               | EitherLeft (LocatedExpr loc)
               | EitherRight (LocatedExpr loc)
               | IndEither (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc) (LocatedExpr loc)
               | Trivial
               | Sole
               | Absurd
               | IndAbsurd (LocatedExpr loc) (LocatedExpr loc)
               | U
               | TODO
  deriving (Eq, Show)

data Core = CThe Core Core
          | CVar Symbol
          | CAtom
          | CTick Symbol
          | CSigma Symbol Core Core
          | CCons Core Core
          | CCar Core
          | CCdr Core
          | CPi Symbol Core Core
          | CLambda Symbol Core
          | CApp Core Core
          | CNat
          | CZero
          | CAdd1 Core
          | CWhichNat Core Core Core Core
          | CIterNat Core Core Core Core
          | CRecNat Core Core Core Core
          | CIndNat Core Core Core Core
          | CList Core
          | CListNil
          | CListCons Core Core
          | CRecList Core Core Core Core
          | CIndList Core Core Core Core
          | CVec Core Core
          | CVecNil
          | CVecCons Core Core
          | CVecHead Core
          | CVecTail Core
          | CIndVec Core Core Core Core Core
          | CEq Core Core Core
          | CSame Core
          | CSymm Core
          | CCong Core Core Core
          | CReplace Core Core Core
          | CTrans Core Core
          | CIndEq Core Core Core
          | CEither Core Core
          | CLeft Core
          | CRight Core
          | CIndEither Core Core Core Core
          | CTrivial
          | CSole
          | CAbsurd
          | CIndAbsurd Core Core
          | CU
          | CTODO Loc Core
  deriving (Eq, Show)

data TopLevel a = Claim (Located Symbol) a
                | Define (Located Symbol) a
                | CheckSame a a a
                | Example a
  deriving Show

data Value = VAtom
           | VTick Symbol
           | VSigma Symbol Value (Closure Value)
           | VCons Value Value
           | VPi Symbol Value (Closure Value)
           | VLambda Symbol (Closure Value)
           | VNat
           | VZero
           | VAdd1 Value
           | VList Value
           | VListNil
           | VListCons Value Value
           | VVec Value Value
           | VVecNil
           | VVecCons Value Value
           | VEq Value Value Value
           | VSame Value
           | VEither Value Value
           | VLeft Value
           | VRight Value
           | VTrivial
           | VSole
           | VAbsurd
           | VU
           | VNeu Value Neutral
  deriving Show

data Neutral = NVar Symbol
             | NCar Neutral
             | NCdr Neutral
             | NApp Neutral Normal
             | NWhichNat Neutral Normal Normal
             | NIterNat Neutral Normal Normal
             | NRecNat Neutral Normal Normal
             | NIndNat Neutral Normal Normal Normal
             | NRecList Neutral Normal Normal
             | NIndList Neutral Normal Normal Normal
             | NHead Neutral
             | NTail Neutral
             | NIndVec12 Neutral Neutral Normal Normal Normal
             | NIndVec2 Normal Neutral Normal Normal Normal
             | NSymm Neutral
             | NCong Neutral Normal
             | NReplace Neutral Normal Normal
             | NTrans1 Neutral Normal
             | NTrans2 Normal Neutral
             | NTrans12 Neutral Neutral
             | NIndEq Neutral Normal Normal
             | NIndEither Neutral Normal Normal Normal
             | NIndAbsurd Neutral Normal
             | NTODO Loc Value
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
              | ClaimAt Loc
              | BoundAt Loc
              | ExampleOut Core
              | FoundTODO (Bwd (Symbol, Maybe Loc, Core)) Core
  deriving Eq


newtype ElabErr = ElabErr (Located [MessagePart Core])
  deriving Show

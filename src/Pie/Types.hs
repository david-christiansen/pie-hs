{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Basic datatypes and operations on them that are used throughout
-- Pie.
module Pie.Types (
  -- * Identifiers and atoms
  Symbol(..), sym, pieKeywords,
  -- * High-level expressions
  Expr(..),
  Expr'(..),
  LocatedExpr(..),
  OutExpr(..),
  describeExpr,
  -- ** Source Locations
  Pos(..),
  Positioned(..),
  Loc(..),
  printLoc,
  Located(..),
  getLoc,
  unLocate,
  spanLocs,
  -- * Core expressions
  Core(..),
  -- * Values
  Normal(..),
  Value(..),
  Env,
  Closure(..),
  Neutral(..),
  -- * Top-level declarations
  TopLevel(..),
  -- * Output from Pie
  -- ** Non-error output
  ElabInfo(..),
  -- ** Error messages
  ElabErr(..),
  MessagePart(..),
  -- * Utility data structures
  Bwd(..)
  ) where

import Data.List.NonEmpty (NonEmpty)
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T

import Pie.Panic

-- | A backwards list that grows to the right.
data Bwd a = None | Bwd a :> a
  deriving (Eq, Ord, Show)

instance Functor Bwd where
  fmap f None = None
  fmap f (xs :> x) = fmap f xs :> f x


-- | An identifer or atom name.
newtype Symbol = Symbol { symbolName :: Text }
  deriving (Eq, Ord)

instance Show Symbol where
  showsPrec p (Symbol x) =
    showParen (p > 10) (showString ("Symbol \"" ++  T.unpack x ++ "\""))

-- | Convert a string into an identifier.
sym :: String -> Symbol
sym = Symbol . T.pack

-- | All the keywords of Pie that are ineligible for use as variable names.
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

-- | A single point in a source file, identified by line and column number
data Pos = Pos { posLine :: Int, posCol :: Int }
  deriving (Eq)

instance Show Pos where
  showsPrec p (Pos line col) =
    showParen (p > 10) (showString "Pos " . shows line . showString " " . shows col)

instance Ord Pos where
  compare (Pos l1 c1) (Pos l2 c2) =
    compare l1 l2 <> compare c1 c2

-- | A source point attached to some data.
data Positioned a = Positioned Pos a
  deriving (Eq, Show)

-- | Describe a source position.
printPos :: Pos -> Text
printPos pos =
  T.pack (show (posLine pos)) <>
  T.pack "." <>
  T.pack (show (posCol pos))

-- | A span in a source file.
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

-- | Describe a source span.
printLoc :: Loc -> Text
printLoc (Loc source start end) =
  T.pack (source ++ ":") <>
  printPos start <>
  T.pack "-" <>
  printPos end


-- | Construct a Loc that contains two other Locs.
--
-- They should be non-overlapping regions where the first argument
-- ends before the second starts in same file
spanLocs :: Loc -> Loc -> Loc
spanLocs (Loc src p1 _) (Loc _ _ p2) = Loc src p1 p2

-- | A location associated with some data.
data Located a = Located Loc a
  deriving (Eq, Show)

instance Functor Located where
  fmap f (Located loc x) = Located loc (f x)

-- | Get the location of a located datum.
getLoc :: Located a -> Loc
getLoc (Located loc _) = loc

-- | Strip the location from a located datum.
unLocate :: Located a -> a
unLocate (Located _ x) = x


-- | An expression with a particular type of source location.
data LocatedExpr loc = Expr loc (Expr' loc)
  deriving (Eq, Show)

-- | High-level expressions resulting from the parser have accurate source spans.
type Expr = LocatedExpr Loc

-- | Expressions resulting from Pie's internals, such as normal forms
-- to be displayed to users, do not have any interesting source
-- information.
type OutExpr = LocatedExpr ()

-- | Each high-level expression in Pie.
data Expr' loc
  = The (LocatedExpr loc) (LocatedExpr loc)
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

-- | Construct a human-readable summary of an expression, suitable for
-- error messages.
describeExpr :: Expr' loc -> Text
describeExpr (The _ _) = T.pack "a type annotation"
describeExpr (Var x) = T.pack "the variable " <> symbolName x
describeExpr Atom = T.pack "Atom"
describeExpr (Tick a) = T.pack "'" <> symbolName a
describeExpr (Pair _ _) = T.pack "a Pair-expression"
describeExpr (Sigma _ _) = T.pack "a Σ-expression"
describeExpr (Cons _ _) = T.pack "a cons-expression"
describeExpr (Car _) = T.pack "a car-expression"
describeExpr (Cdr _) = T.pack "a cdr-expression"
describeExpr (Arrow _ _) = T.pack "an arrow-expression"
describeExpr (Pi _ _) = T.pack "a Π-expression"
describeExpr (Lambda _ _) = T.pack "a λ-expression"
describeExpr (App _ _) = T.pack "a function application"
describeExpr Nat = T.pack "Nat"
describeExpr Zero = T.pack "zero"
describeExpr (Add1 _) = T.pack "an add1-expression"
describeExpr (NatLit n) = T.pack "the natural number" <> T.pack (show n)
describeExpr (WhichNat _ _ _) = T.pack "a which-Nat-expression"
describeExpr (IterNat _ _ _) = T.pack "an iter-Nat-expression"
describeExpr (RecNat _ _ _) = T.pack "a rec-Nat-expression"
describeExpr (IndNat _ _ _ _) = T.pack "an ind-Nat-expression"
describeExpr (List _) = T.pack "a List type"
describeExpr ListNil = T.pack "the empty list nil"
describeExpr (ListCons _ _) = T.pack "a ::-expression"
describeExpr (RecList _ _ _) = T.pack "a rec-List-expression"
describeExpr (IndList _ _ _ _) = T.pack "an ind-List-expression"
describeExpr (Vec _ _) = T.pack "a Vec type"
describeExpr VecNil = T.pack "the empty Vec vecnil"
describeExpr (VecCons _ _) = T.pack "a vec::-expression"
describeExpr (VecHead _) = T.pack "a head-expression"
describeExpr (VecTail _) = T.pack "a tail-expression"
describeExpr (IndVec _ _ _ _ _) = T.pack "an ind-Vec-expression"
describeExpr (Eq _ _ _) = T.pack "an =-expression"
describeExpr (Same _) = T.pack "a same-expression"
describeExpr (Symm _) = T.pack "a symm-expression"
describeExpr (Cong _ _) = T.pack "a cong-expression"
describeExpr (Replace _ _ _) = T.pack "a replace-expression"
describeExpr (Trans _ _) =  T.pack "a trans-expression"
describeExpr (IndEq _ _ _) = T.pack "an ind-Eq-expression"
describeExpr (Either _ _) = T.pack "an Either type"
describeExpr (EitherLeft _) = T.pack "a left-expression"
describeExpr (EitherRight _) = T.pack "a right-expression"
describeExpr (IndEither _ _ _ _) = T.pack "an ind-Either-expression"
describeExpr Trivial = T.pack "Trivial"
describeExpr Sole = T.pack "sole"
describeExpr Absurd = T.pack "Absurd"
describeExpr (IndAbsurd _ _) =  T.pack "an ind-Absurd-expression"
describeExpr U = T.pack "U"
describeExpr TODO = T.pack "a TODO marker"

-- | Core expressions, produced as a result of type checking and
-- elaboration. Core expressions are simpler that high-level expressions 'Expr'.
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

-- | Top-level declarations in a Pie source file
data TopLevel a = Claim (Located Symbol) a
                | Define (Located Symbol) a
                | CheckSame a a a
                | Example a
  deriving Show

-- | Values are the result of evaluation. They represent βι normal
-- forms. The η-expansion occurs during reading back of values into
-- expressions.
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

-- | Neutral expressions in which all possible computation has been
-- carried out, but the final value is waiting on the value of a free
-- variable or the completion of a TODO.
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

-- | A representation of normal forms. A value and its type is
-- sufficient information to reconstruct the value's normal form with
-- respect to its type.
data Normal = NThe { normType :: Value, normVal :: Value }
  deriving Show

-- | Binding information is represented by closures, in which the free
-- variables of an expression are assigned values by an environment.
data Closure a = Closure (Env a) Core
  deriving Show

-- | Run-time environments map free variables to their values.
type Env a = Bwd (Symbol, a)

-- | Error messages can contain either bits of text or data to be
-- displayed. The data is typically an expression to be
-- pretty-printed.
data MessagePart a = MText Text | MVal a
  deriving (Eq, Show)

instance Functor MessagePart where
  fmap f (MText txt) = MText txt
  fmap f (MVal x) = MVal (f x)

-- | Information constructed during elaboration, and displayed when
-- running Pie in verbose mode.
data ElabInfo
  = ExprHasType Core
  | ExprIsType
  | ExprWillHaveType Core -- ^ TODOs
  | ClaimAt Loc
  | BoundAt Loc
  | ExampleOut Core
  | FoundTODO (Bwd (Symbol, Maybe Loc, Core)) Core
  deriving Eq

-- | Errors produced during elaboration consist of a source location
-- and a message.
newtype ElabErr = ElabErr (Located [MessagePart Core])
  deriving (Eq, Show)

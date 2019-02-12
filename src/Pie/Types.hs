module Pie.Types where

import Data.List.NonEmpty (NonEmpty)
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T

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
  deriving Show

data Positioned a = Positioned Pos a
  deriving Show

printPos :: Pos -> Text
printPos pos =
  T.pack (show (posLine pos)) <>
  T.pack "." <>
  T.pack (show (posCol pos))

data Loc = Loc { locSource :: FilePath
               , locStart :: Pos
               , locEnd :: Pos
               }
  deriving Show

printLoc :: Loc -> Text
printLoc loc =
  T.pack (locSource loc ++ ":") <>
  printPos (locStart loc) <>
  T.pack "-" <>
  printPos (locEnd loc)

data Located a = Located Loc a
  deriving Show

newtype Expr = Expr (Located (Expr' Expr))
  deriving Show

newtype OutExpr = OutExpr (Expr' OutExpr)

data Expr' e = Tick Symbol
             | Atom
             | Zero
             | Add1 e
             | IndNat e e e e
             | Nat
             | Var Symbol
             | Arrow e (NonEmpty e)
             | Pi (NonEmpty (Symbol, e)) e
             | Lambda (NonEmpty Symbol) e
             | App e e [e]
             | Sigma (NonEmpty (Symbol, e)) e
             | Pair e e
             | Cons e e
             | Car e
             | Cdr e
             | Trivial
             | Sole
             | Eq e e e
             | Same e
             | Replace e e e
             | Trans e e
             | Cong e e
             | Symm e
             | IndEq e e e
             | Vec e e
             | VecNil
             | VecCons e e
             | VecHead e
             | VecTail e
             | IndVec e e e e e
             | U
             | The e e
  deriving Show

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

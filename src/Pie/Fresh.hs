{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Generating fresh variable names.
module Pie.Fresh (freshen) where

import Data.Char
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T

import Pie.Types

-- | Generate a fresh name, using a provided name as a starting
-- point. The result name will not occur in the list of used names
-- provided.
freshen ::
  [Symbol] {- ^ The used names to avoid -} ->
  Symbol {- ^ The name to start with -} ->
  Symbol
freshen used x =
  if x `elem` used
    then let split = splitName (symbolName x)
         in freshen' used split
    else x

freshen' :: [Symbol] -> (Text, Integer) -> Symbol
freshen' used split =
  let joined = unsplitName split
  in if joined `elem` used
       then freshen' used (nextSplitName split)
       else joined

nameRegex = T.pack "^((?:[\\p{Letter}[0-9]]*[\\p{Letter}])?)([0-9₀₁₂₃₄₅₆₇₈₉]*)$"

isNameDigit :: Char -> Bool
isNameDigit c = c `elem` "0123456789₀₁₂₃₄₅₆₇₈₉"

splitName t =
  let backwards = reverse (T.unpack t)
      (digits, others) = span isNameDigit backwards
      x = case reverse others of
            [] -> "x"
            nonEmpty -> nonEmpty
      i = case reverse digits of
            [] -> 1
            nonEmpty -> read (asNonSubscript nonEmpty)
  in (T.pack x, i)

nextSplitName :: (txt, Integer) -> (txt, Integer)
nextSplitName (base, i) = (base, i + 1)

unsplitName :: (Text, Integer) -> Symbol
unsplitName (base, i) =
  Symbol (base <> asSubscript i)

asNonSubscript i = map fromSub i
  where
    fromSub c =
      case lookup c nonSubscripts of
        Just c' -> c'
        Nothing -> c

asSubscript i = T.pack (map toSub (show i))
  where
    toSub c =
      case lookup c subscriptDigits of
        Just c' -> c'
        Nothing -> c

subscriptDigits =
  [ ('0', '₀')
  , ('1', '₁')
  , ('2', '₂')
  , ('3', '₃')
  , ('4', '₄')
  , ('5', '₅')
  , ('6', '₆')
  , ('7', '₇')
  , ('8', '₈')
  , ('9', '₉')
  ]

nonSubscripts = map swap subscriptDigits
  where
    swap (x, y) = (y, x)

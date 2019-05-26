{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Generating fresh variable names.
module Pie.Fresh (freshen) where

import Data.Char
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.ICU

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

splitName :: Text -> (Text, Integer)
splitName t =
  case find (regex [] nameRegex) t of
    Just m ->
      let x = case group 1 m of
                Just y
                  | y == T.empty -> T.pack "x"
                  | otherwise -> y
                Nothing -> T.pack "x"
          n = case group 2 m of
                Just i
                  | i == T.empty -> 1
                  | otherwise -> read (asNonSubscript (T.unpack i))
                Nothing -> 1
      in (x, n)
    Nothing -> (t, 1)


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

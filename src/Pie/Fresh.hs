{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Pie.Fresh (freshen) where

import Data.Char
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.ICU

import Pie.Types

freshen :: [Symbol] -> Symbol -> Symbol
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

splitName :: Text -> (Text, Integer)
splitName t =
  case find (regex [] nameRegex) t of
    Just m ->
      case (group 0 m, group 1 m) of
        (Just x, Just i) -> (x, read (T.unpack i))
        (Just x, Nothing) -> (x, 0)
        _ -> (t, 0)
    Nothing -> (t, 0)
  where
    nameRegex = (T.pack "^([\\p{Letter}[0-9]]*[\\p{Letter}])([0-9]*₀₁₂₃₄₅₆₇₈₉)$")


nextSplitName :: (txt, Integer) -> (txt, Integer)
nextSplitName (base, i) = (base, i + 1)

unsplitName :: (Text, Integer) -> Symbol
unsplitName (base, i) =
  Symbol (base <> asSubscript i)

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

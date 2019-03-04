{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Pie.Panic where

panic :: String -> a
panic msg = error ("Internal error in Pie: " ++ msg)

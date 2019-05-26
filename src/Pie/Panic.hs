{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Utilities for early termination.
module Pie.Panic where

-- | Terminate Pie with a particular message. This indicates a bug.
panic :: String -> a
panic msg = error ("Internal error in Pie: " ++ msg)

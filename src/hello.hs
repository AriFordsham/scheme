{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import Data.Bifunctor
import Data.Maybe

main = putStrLn "Hello, World!"

data Datum
  = Bool Bool
  | Char Char
  | Null
  | Number Int
  | Pair Datum Datum
  | Symbol String


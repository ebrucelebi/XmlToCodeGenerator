{-# OPTIONS --guardedness #-}

module main where

open import Data.Bool
open import Data.String
open import Data.List
open import Data.Maybe
open import Data.Product
open import IO
open import readIMODEFile
open import checkProject

main : Bool × (List String)
main = checkProject readIMODEFiles

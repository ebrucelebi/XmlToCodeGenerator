{-# OPTIONS --safe #-}

module main where

open import Data.Bool
open import Data.String
open import Data.List
open import Data.Maybe
open import Data.Product
open import readIMODEFile
open import codeGeneration

main : Bool × (List String)
main = checkAndGenerateCode readIMODEFiles "logicModel1"

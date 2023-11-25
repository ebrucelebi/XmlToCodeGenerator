{-# OPTIONS --safe #-}

module main where

open import readIMODEFile
open import codeGeneration

open import Data.Bool
open import Data.String
open import Data.List
open import Data.Product

main : Bool × (List String)
main = checkAndGenerateCode readIMODEFiles "logicModel1"

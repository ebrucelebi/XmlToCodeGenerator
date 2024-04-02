{-# OPTIONS --safe #-}

module main where

open import readIMODEFile
open import codeGeneration
open import IMODEDataTypes

open import Data.Bool
open import Data.String
open import Data.List
open import Data.Product
open import Data.Maybe

main : String -> CodeGenerationResult
main n = checkGenerateAndVerify readIMODEFiles n

getModel : String -> Maybe Model
getModel s with readIMODEFiles
... | nothing = nothing
... | just p = findModelInProjectWithName p s

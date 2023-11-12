{-# OPTIONS --safe #-}

module codeGeneration where

open import Data.String
open import Data.Maybe
open import Data.Bool
open import Data.Product
open import Data.List
open import IMODEDataTypes
open import checkProject

generateModelElements : Project -> List ModelElement -> List String

generateModelElement : Project -> ModelElement -> List String
generateModelElement p (OutputInstance _ _) = "Output" ∷ []
generateModelElement p (Addition _) = "Addition" ∷ []
generateModelElement p (InputInstance _ _) = "Input" ∷ []
generateModelElement p _ = []

generateModelElements _ [] = []
generateModelElements p (m ∷ ms) = concatenateTwoList (generateModelElement p m) (generateModelElements p ms)

collectEndModelElements : List ModelElement -> List ModelElement
collectEndModelElements [] = []
collectEndModelElements (m ∷ ms) with m
... | (OutputInstance _ _) = m ∷ collectEndModelElements ms
... | _ = collectEndModelElements ms

generateModel : Project -> Model -> List String
generateModel p (Operation _ _ _ sms) = generateModelElements p (collectEndModelElements sms)
generateModel _ _ = []

generateCode : Project -> String -> Bool × (List String)
generateCode p n with findModelInProjectWithName p n
... | nothing = false , concatenateStrings ("Could not find the root model " ∷ n ∷ []) ∷ []
... | just m = true , generateModel p m

checkAndGenerateCode : Maybe Project -> String -> Bool × (List String)
checkAndGenerateCode p n with checkProject p | p
... | true , _ | just project = (generateCode project n)
... | result | _ = result


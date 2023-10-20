{-# OPTIONS --guardedness #-}

module checkProject where

open import Data.Bool
open import Data.String
open import Data.List
open import Data.Maybe
open import Data.Product
open import IMODEDataTypes

checkType : Type -> List String
checkType (iUserDefined n iNull) = ("Type " Data.String.++ n Data.String.++ " is null.") ∷ []
checkType _ = []

checkTypes : List Type -> List String
checkTypes [] = []
checkTypes (t ∷ ts) = (checkType t) Data.List.++ (checkTypes ts)

checkProject : Maybe Project -> Bool × (List String)
checkProject nothing = false , "Project load failed." ∷ []
checkProject (just record {types = ts}) with checkTypes ts
... | [] = true , []
... | errors = false , errors

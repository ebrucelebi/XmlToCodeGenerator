{-# OPTIONS --safe #-}
module IMODEScannedDataTypes where

open import IMODEDataTypes

open import Data.String
open import Data.List
open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.Maybe
open import Data.Vec
open import Data.Empty
open import Data.Unit
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Graph.Acyclic

max : ℕ -> ℕ -> ℕ
max zero m = m
max n zero = n
max (suc n) (suc m) = suc (max n m)

data ModelDAG : ℕ → Set where
  -- TestDAG : {n : ℕ} -> String -> ModelDAG n
  ∅   : {n : ℕ} -> ModelDAG n
  _&_ : ∀ {n} (c : Context ModelElement ModelElement n) (g : ModelDAG n) →
        ModelDAG (suc n)

data ModelTree : ℕ -> Set where -- upper bound
  ExampleTree : {n : ℕ} -> String -> ModelTree n
  Leaf : {n : ℕ} -> ModelElement -> ModelTree n
  _∷_ : ∀ {n} (parent : ModelElement) (children : List (ModelTree n)) -> ModelTree (suc n)
  Root : ∀ {n} (xs : List (ModelTree n)) -> ModelTree n

depth : ∀ {n} -> ModelTree n -> ℕ
depth {n = n} _ = n

--checkAdditionInputs : ModelElement -> Bool

--checkAdditionInputsProof : checkAdditionInputs (Addition []) ≡ false
--checkAdditionInputsProof = refl

--checkAdditionInputsProof : checkAdditionInputs (Addition (a ∷ [])) ≡ false
--checkAdditionInputsProof = refl

--checkAdditionInputsProof : checkAdditionInputs (Addition (a ∷ b ∷ xs)) ≡ true
--checkAdditionInputsProof = refl

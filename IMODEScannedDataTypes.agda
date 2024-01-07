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

data ModelDAG : ℕ → Set where
  -- TestDAG : {n : ℕ} -> String -> ModelDAG n
  ∅   : {n : ℕ} -> ModelDAG n
  _&_ : ∀ {n} (c : Context ModelElement ModelElement n) (g : ModelDAG n) →
        ModelDAG (suc n)

DAGToList : ∀ {n} -> ModelDAG n -> List ModelElement
DAGToList ∅ = []
DAGToList ((context me e) & dag) = me ∷ (DAGToList dag)

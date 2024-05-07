{-# OPTIONS --safe #-}
module ModelDAG where

open import IMODEDataTypes

open import Data.String
open import Data.List
open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Data.Unit
open import Data.Fin
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Graph.Acyclic hiding (reverse)

data ModelDAG : ℕ → Set where
  -- TestDAG : {n : ℕ} -> String -> ModelDAG n
  ∅   : {n : ℕ} -> ModelDAG n
  _&_ : ∀ {n} (c : Context ModelElement ModelElement n) (g : ModelDAG n) →
        ModelDAG (suc n)

DAGToList : ∀ {n} -> ModelDAG n -> List ModelElement
DAGToList ∅ = []
DAGToList ((context me e) & dag) = me ∷ (DAGToList dag)

DAGsToListReverse : ∀ {n} -> List (ModelDAG n) -> List ModelElement
DAGsToListReverse [] = []
DAGsToListReverse (dag ∷ dags) = appendUniqueModelElement (reverse (DAGToList dag)) (DAGsToListReverse dags)

sub : (n : ℕ) -> Fin n -> ℕ
sub zero _ = zero
sub n zero = n
sub (suc n) (suc i) = sub n i

getEdgeDestination : ∀ {n} -> ModelDAG n -> ((me , i) : ModelElement × Fin n) -> ModelDAG (sub n i)
getEdgeDestination ∅ _ = ∅
getEdgeDestination dag (_ , zero) = dag
getEdgeDestination (c & dag) (me , suc n) = getEdgeDestination dag (me , n)

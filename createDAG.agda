{-# OPTIONS --safe #-}

module createDAG where

open import IMODEDataTypes
open import ModelDAG

open import Data.Bool
open import Data.String
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Nat
open import Data.Vec
open import Data.Fin
open import Data.Graph.Acyclic

findIndexWithId : ∀ {n} -> Vec ModelElement n -> String -> Maybe (Fin n)
findIndexWithId [] _ = nothing
findIndexWithId (x ∷ xs) id with getBaseModelProperties x
... | nothing = nothing
... | just (Properties _ id2 _ _ ) with id == id2
... | true = just zero
... | false with findIndexWithId xs id
... | just i = just (suc i)
... | nothing = nothing

findEndModels : List ModelElement -> List ModelElement
findEndModels [] = []
findEndModels (x ∷ xs) with getBaseModelProperties x
... | just (Properties _ _ _ []) = x ∷ findEndModels xs
... | _ = findEndModels xs

findDepthUpperBound : Model -> ℕ
findDepthUpperBound (Operation _ _ _ sm) = Data.List.length sm

findNonConnectionModelElementCountAlt : List ModelElement -> ℕ
findNonConnectionModelElementCountAlt [] = zero
findNonConnectionModelElementCountAlt ((Connection _ _ _ _) ∷ xs) = findNonConnectionModelElementCountAlt xs
findNonConnectionModelElementCountAlt (x ∷ xs) = suc (findNonConnectionModelElementCountAlt xs)

findNonConnectionModelElementCount : Model -> ℕ
findNonConnectionModelElementCount (Operation _ _ _ sm) = findNonConnectionModelElementCountAlt sm

findModelsWithIds : Model -> List String -> Maybe (List ModelElement)
findModelsWithIds _ [] = just []
findModelsWithIds m (x ∷ xs) with findModelElementInModelWithID m x | findModelsWithIds m xs
... | just me | just mes = just (me ∷ mes)
... | _ | _ = nothing

appendUnique : List ModelElement -> List ModelElement -> List ModelElement
appendUnique [] l = l
appendUnique l [] = l
appendUnique (x ∷ xs) l with containsModelElement (appendUnique xs l) x
... | true = (appendUnique xs l)
... | false = x ∷ (appendUnique xs l)

mutual
    topologicalListAlt2 : Model -> List ModelElement -> ℕ -> ModelElement -> Maybe (List ModelElement)
    topologicalListAlt2 m seen zero me = just (me ∷ [])
    topologicalListAlt2 m seen (suc n) (Connection _ _ startMID _ ) with findModelElementInModelWithID m startMID
    topologicalListAlt2 m seen (suc n) c | nothing = nothing
    topologicalListAlt2 m seen (suc n) c | just startM = topologicalListAlt2 m (c ∷ seen) n startM
    topologicalListAlt2 m seen (suc n) me with containsModelElement seen me
    ... | true = just (me ∷ [])
    ... | false with getBaseModelProperties me
    ... | nothing = nothing
    ... | just (Properties _ _ [] _) = just (me ∷ [])
    ... | just (Properties _ _ inConIds _) with findModelsWithIds m inConIds
    ... | nothing = nothing
    ... | just inCons with topologicalListAlt m (me ∷ seen) n inCons
    ... | nothing = nothing
    ... | just ts = just (me ∷ ts)

    topologicalListAlt : Model -> List ModelElement -> ℕ -> List ModelElement -> Maybe (List ModelElement)
    topologicalListAlt _ _ _ [] = just []
    topologicalListAlt m seen n (x ∷ xs) with topologicalListAlt2 m seen n x | topologicalListAlt m seen n xs 
    ... | just l1 | just l2 = just (appendUnique l1 l2)
    ... | _ | _ = nothing

topologicalList : (m : Model) -> Maybe (List ModelElement)
topologicalList (Operation a b c sm) = topologicalListAlt (Operation a b c sm) [] (Data.List.length sm) (findEndModels sm)

DAGIndexOfModelElement : ∀ {n} -> ModelDAG n -> ModelElement -> Maybe (Fin n)
DAGIndexOfModelElement ∅ _ = nothing
DAGIndexOfModelElement ((context m1 l) & ms) m2 with (getModelElementID m1) == (getModelElementID m2)
... | true = just zero
... | false with DAGIndexOfModelElement ms m2
... | nothing = nothing
... | just n = just (suc n)

createEdge : ∀ {n} -> Model -> ModelElement -> ModelDAG n -> Maybe (ModelElement × Fin n)
createEdge m (Connection _ _ startMID _ ) dag with findModelElementInModelWithID m startMID
createEdge m c dag | nothing = nothing
createEdge m c dag | just startM with DAGIndexOfModelElement dag startM
... | nothing = nothing
... | just i = just (c , i)
createEdge _ _ _ = nothing

createEdges : ∀ {n} -> Model -> List ModelElement -> ModelDAG n -> Maybe (List (ModelElement × Fin n))
createEdges _ [] _ = just []
createEdges m (me ∷ ms) dag with createEdge m me dag | createEdges m ms dag
... | just e | just es = just (e ∷ es)
... | _ | _ = nothing 

addEdges : ∀ {n} -> Model -> ModelDAG n -> Maybe (ModelDAG n)
addEdges m ∅ = just ∅
addEdges m ((context me l) & dag) with addEdges m dag
... | nothing = nothing
... | just newDag with getBaseModelProperties me
... | nothing = nothing
... | just (Properties _ _ [] _) = just ((context me l) & newDag)
... | just (Properties _ _ inConIds _) with findModelsWithIds m inConIds
... | nothing = nothing
... | just inCons with createEdges m inCons dag
... | nothing = nothing
... | just es  = just ((context me es) & newDag)

createContexts : List ModelElement -> (n : ℕ) -> ModelDAG n
createContexts [] _ = ∅
createContexts _ zero = ∅
createContexts (m ∷ ms) (suc n) = (context m []) & (createContexts ms n)

createDAG : (m : Model) -> Maybe (ModelDAG (findNonConnectionModelElementCount m))
createDAG m with (topologicalList m)
... | nothing = nothing
... | just l = addEdges m (createContexts l (findNonConnectionModelElementCount m))
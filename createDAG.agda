{-# OPTIONS --safe #-}

module createDAG where

open import IMODEDataTypes
open import ModelDAG

open import Data.Bool
open import Data.String hiding(_++_)
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Graph.Acyclic

mutual
    -- (Parent model) ->
    -- (Count previous as inputs)
    -- (Model elements that are alreaday added to the list for the current path) ->
    -- (A count down from total model element to eliminate termination error) ->
    -- (Model element to start/continue the topological order)
    -- (Final topological order starting with given model element)
    topologicalListAlt2 : Model -> Bool -> List ModelElement -> ℕ -> ModelElement -> Maybe (List ModelElement)
    topologicalListAlt2 m _ seen zero me = just (me ∷ []) -- If count down is finished return final model element.
    -- If it is a connection, find what model element it is coming from and continue with that model element. Do not add connection.
    topologicalListAlt2 m true seen (suc n) (Previous p v) with containsModelElement seen (Previous p v)
    ... | true = just [] -- It is the previous at athe beginning
    ... | false = just ((Previous p v) ∷ []) -- Treat previous as inputs and end here.
    topologicalListAlt2 m prevAsInput seen (suc n) (Connection _ _ startMID _ ) with findModelElementInModelWithID m startMID
    topologicalListAlt2 m prevAsInput seen (suc n) c | nothing = nothing
    topologicalListAlt2 m prevAsInput seen (suc n) c | just startM = topologicalListAlt2 m prevAsInput (seen) n startM
    -- If the model element is already added to the list from this path, it is a cycle. Add the model element but do not continue. Leave the error logging to the check.
    topologicalListAlt2 m true seen (suc n) me with containsModelElement seen me
    ... | true = just (me ∷ []) -- Cycle
    ... | false with getBaseModelProperties me -- It should have properties if it is not a connection.
    ... | nothing = nothing -- Should not come here. If that's the case load is wrong.
    ... | just (Properties _ _ [] _ []) = just (me ∷ []) -- No input connections. Path ends here.
    ... | just (Properties _ _ inConIds _ condConIds) with findModelElementsInModelWithID m condConIds | findModelElementsInModelWithID m inConIds -- Find model elements ofinput connections
    ... | nothing | _ = nothing
    ... | _ | nothing = nothing
    ... | just inCons | just condCons with topologicalListAlt m true (me ∷ seen) n (inCons Data.List.++ condCons)
    ... | nothing = nothing
    ... | just ts = just (me ∷ ts)
    topologicalListAlt2 m false seen (suc n) me with getBaseModelProperties me -- It should have properties if it is not a connection.
    topologicalListAlt2 m false seen (suc n) me | nothing = nothing -- Should not come here. If that's the case load is wrong.
    topologicalListAlt2 m false seen (suc n) me | just (Properties _ _ inConIds _ condConIds) with me | findModelElementsInModelWithID m condConIds | findModelElementsInModelWithID m inConIds -- Find model elements ofinput connections
    topologicalListAlt2 m false seen (suc n) me | just p | _ | nothing | _ = nothing
    topologicalListAlt2 m false seen (suc n) me | just p | _ | _ | nothing = nothing
    topologicalListAlt2 m false seen (suc n) me | just p | (Previous _ _) | just inCons | just condCons with topologicalListAlt m true (me ∷ seen) n (inCons Data.List.++ condCons) -- Continue to the path with input connections. prevAsInput certainly false
    topologicalListAlt2 m false seen (suc n) me | just p | (Previous _ _) | just inCons | just condCons | nothing = nothing
    topologicalListAlt2 m false seen (suc n) me | just p | (Previous _ _) | just inCons | just condCons | just ts = just (me ∷ ts)
    topologicalListAlt2 m false seen (suc n) me | just p | _ | just inCons | just condCons = topologicalListAlt m false (me ∷ seen) n (inCons Data.List.++ condCons) -- Continue to the path with input connections.

    -- (Parent model) ->
    -- (Model elements that are already added to the list for the current path) ->
    -- (A count down from total model element to eliminate termination error) ->
    -- (Model element list to start/continue the topological order)
    -- (Final topological order list starting with given model elements)
    topologicalListAlt : Model -> Bool -> List ModelElement -> ℕ -> List ModelElement -> Maybe (List ModelElement)
    topologicalListAlt _ _ _ _ [] = just []
    topologicalListAlt m prevAsInput seen n (x ∷ xs) with topologicalListAlt2 m prevAsInput seen n x | topologicalListAlt m prevAsInput seen n xs 
    ... | just l1 | just l2 = just (appendUniqueModelElement l1 l2) -- A model elements might be used in two different paths. Eliminate duplicates.
    ... | _ | _ = nothing

topologicalListForPreviouses : (m : Model) -> ℕ -> List ModelElement -> Maybe (List (List ModelElement))
topologicalListForPreviouses _ _ [] = just []
topologicalListForPreviouses m n (x ∷ xs) with (topologicalListAlt m false [] n (x ∷ [])) | (topologicalListForPreviouses m n xs)
... | just l | just ls = just (l ∷ ls)
... | _ | _ = nothing

-- Creates topological list from the model elements in the model. Does not contain connections. Starts from end model elements (model elements that has no output points).
topologicalList : (m : Model) -> Maybe (List (List ModelElement))
topologicalList (Operation a b c sm) with (topologicalListAlt (Operation a b c sm) true [] (Data.List.length sm) (findEndModels sm)) |
                                          (topologicalListForPreviouses (Operation a b c sm) (Data.List.length sm) (findPreviousModels sm))
topologicalList m | just l1 | just l2 = just (l1 ∷ l2)
topologicalList m | _ | _ = nothing                                      

-- Find the successor range index for the given model element is the given DAG.
DAGIndexOfModelElement : ∀ {n} -> ModelDAG n -> ModelElement -> Maybe (Fin n)
DAGIndexOfModelElement ∅ _ = nothing
DAGIndexOfModelElement ((context m1 l) & ms) m2 with (getModelElementID m1) == (getModelElementID m2)
... | true = just zero
... | false with DAGIndexOfModelElement ms m2
... | nothing = nothing
... | just n = just (suc n)

-- Create edge for the given model element. Model element should be Connection.
createEdge : ∀ {n} -> Model -> ModelElement -> ModelDAG n -> Maybe (ModelElement × Fin n)
createEdge m (Connection _ _ startMID _ ) dag with findModelElementInModelWithID m startMID
createEdge m c dag | nothing = nothing
createEdge m c dag | just startM with DAGIndexOfModelElement dag startM
... | nothing = nothing
... | just i = just (c , i)
createEdge _ _ _ = nothing

-- Create edges for the given model elements. Model elements should be Connection.
createEdges : ∀ {n} -> Model -> List ModelElement -> ModelDAG n -> Maybe (List (ModelElement × Fin n))
createEdges _ [] _ = just []
createEdges m (me ∷ ms) dag with createEdge m me dag | createEdges m ms dag
... | just e | just es = just (e ∷ es)
... | nothing | just es = just es
... | _ | _ = nothing

-- Add edges to the given DAG according to model element in the context.
addEdges : ∀ {n} -> Model -> ModelDAG n -> Maybe (ModelDAG n)
addEdges m ∅ = just ∅
addEdges m ((context me l) & dag) with addEdges m dag
... | nothing = nothing
... | just newDag with getBaseModelProperties me
... | nothing = nothing
... | just (Properties _ _ [] _ []) = just ((context me l) & newDag)
... | just (Properties _ _ inConIds _ condConIds) with findModelElementsInModelWithID m condConIds | findModelElementsInModelWithID m inConIds -- Find model elements ofinput connections
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just inCons | just condCons with createEdges m (inCons Data.List.++ condCons) dag
... | nothing = nothing
... | just es  = just ((context me es) & newDag)

-- Create a DAG with no edges with given list in the same order.
createContexts : List ModelElement -> (n : ℕ) -> ModelDAG n
createContexts [] _ = ∅
createContexts _ zero = ∅
createContexts (m ∷ ms) (suc n) = (context m []) & (createContexts ms n)

completeDAGs : Model -> List (List ModelElement) -> (n : ℕ) -> Maybe (List (ModelDAG n))
completeDAGs _ [] _ = just []
completeDAGs m (l ∷ ls) n with addEdges m (createContexts l n) | completeDAGs m ls n
... | just dag | just dags = just (dag ∷ dags)
... | _ | _ = nothing

-- First get the topological/context order for the DAG then create contexts then add edges to the contexts.
createDAG : (m : Model) -> Maybe (List (ModelDAG (findNonConnectionModelElementCount m)))
createDAG m with (topologicalList m)
... | nothing = nothing
... | just ls = completeDAGs m ls (findNonConnectionModelElementCount m)  
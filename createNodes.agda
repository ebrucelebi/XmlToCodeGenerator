{-# OPTIONS --safe #-}

module createNodes where

open import IMODEDataTypes
open import IMODEScannedDataTypes

open import Data.Bool
open import Data.String
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Nat
open import Data.Vec
open import Data.Fin

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

findDepth : Model -> ℕ
findDepth (Operation _ _ _ sm) = Data.List.length sm

findModelsWithIds : Model -> List String -> Maybe (List ModelElement)
findModelsWithIds _ [] = just []
findModelsWithIds m (x ∷ xs) with findModelElementInModelWithID m x | findModelsWithIds m xs
... | just me | just mes = just (me ∷ mes)
... | _ | _ = nothing

mutual
    createTree : Model -> (n : ℕ) -> ModelElement -> Maybe (ModelTree n)
    createTree m zero me = just (Leaf me)
    createTree m (suc n) (Connection _ _ startMID _ ) with findModelElementInModelWithID m startMID
    createTree m (suc n) c | nothing = just (ExampleTree "createTree4")
    createTree m (suc n) c | just startM with createTree m n startM
    ... | nothing = just (ExampleTree "createTree5")
    ... | just t = just (c ∷ (t ∷ []))
    createTree m (suc n) me with getBaseModelProperties me
    ... | nothing = just (ExampleTree "createTree1")
    ... | just (Properties _ _ [] _) = just (Leaf me)
    ... | just (Properties _ _ inConIds _) with findModelsWithIds m inConIds
    ... | nothing = just (ExampleTree "createTree2")
    ... | just inCons with createTrees m n inCons
    ... | nothing = just (ExampleTree "createTree3")
    ... | just ts = just (me ∷ ts)

    createTrees : Model -> (n : ℕ) -> List ModelElement -> Maybe (List (ModelTree n))
    createTrees m _ [] = just []
    createTrees m n (x ∷ xs) with createTree m n x | createTrees m n xs
    ... | just t | just ts = just (t ∷ ts)
    ... | _ | _ = just (ExampleTree "createTrees" ∷ [])

createModelTree : (m : Model) -> Maybe (ModelTree (findDepth m))
createModelTree (Operation a b c sm) with createTrees (Operation a b c sm) (Data.List.length sm) (findEndModels sm)
... | nothing = just (ExampleTree "createModelTree")
... | just trees = just (Root trees)
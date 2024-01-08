{-# OPTIONS --safe #-}

module codeGeneration where

open import utility
open import IMODEDataTypes
open import IMODEScannedDataTypes
open import createNodes
open import checkProject

open import Data.String
open import Data.Maybe
open import Data.Bool
open import Data.Product
open import Data.List
open import Data.Fin
open import Data.Nat
open import Data.Graph.Acyclic

mutual
    generateEdges : ∀ {n} -> Project -> List (ModelElement × Fin n) -> ModelDAG n -> List String 
    generateEdges _ [] _ = []
    generateEdges p (e ∷ xs) ∅ = []
    generateEdges p ((_ , zero) ∷ xs) dag = concatenateTwoList (generateModelElements p dag) (generateEdges p xs dag)
    generateEdges p ((me , (suc m)) ∷ xs) (c & dag) = concatenateTwoList (generateEdges p ((me , m) ∷ []) dag) (generateEdges p xs (c & dag))

    generateModelElement : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateModelElement p (context (OutputInstance _ _) edges) dag = "Output" ∷ generateEdges p edges dag
    generateModelElement p (context (Addition _) edges) dag = "Addition" ∷ generateEdges p edges dag
    generateModelElement p (context (Multiplication _) edges) dag = "Multiplication" ∷ generateEdges p edges dag
    generateModelElement p (context (InputInstance _ _) edges) dag = "Input" ∷ generateEdges p edges dag
    generateModelElement p _ _ = []

    generateModelElements : ∀ {n} -> Project -> ModelDAG n -> List String
    generateModelElements _ ∅ = []
    generateModelElements p (c & dag) = concatenateTwoList (generateModelElement p c dag) (generateModelElements p dag)

collectEndModelElements : List ModelElement -> List ModelElement
collectEndModelElements [] = []
collectEndModelElements (m ∷ ms) with m
... | (OutputInstance _ _) = m ∷ collectEndModelElements ms
... | _ = collectEndModelElements ms

generateModel : Project -> Model -> List String
generateModel p (Operation n ins outs sms) with (createDAG (Operation n ins outs sms))
... | nothing = []
... | just dag = generateModelElements p dag

generateCode : Project -> String -> Bool × (List String)
generateCode p n with findModelInProjectWithName p n
... | nothing = false , concatenateStrings ("Could not find the root model " ∷ n ∷ []) ∷ []
... | just m = true , generateModel p m

checkAndGenerateCode : Maybe Project -> String -> Bool × (List String)
checkAndGenerateCode p n with checkProject p | p
... | true , _ | just pro = (generateCode pro n)
... | result | _ = result

denemeGen : List String
denemeGen = generateModel (project "" [] [] [] []) exampleModel
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

data CodeSection : Set where
    Identifier : CodeSection
    Main : CodeSection

mutual
    generateEdges : ∀ {n} -> Project -> List ModelElement -> CodeSection -> List (ModelElement × Fin n) -> ModelDAG n -> (List String) × (List ModelElement)
    generateEdges _ seen _ [] _ = ([] , seen)
    generateEdges p seen _ (e ∷ xs) ∅ = ([] , seen)
    
    generateEdges p seen section (e ∷ xs) (c & dag) with generateEdges p seen section xs (c & dag)
    generateEdges p seen section (e ∷ xs) (c & dag) | (res1 , seen1) with e
    generateEdges p seen section (e ∷ xs) (c & dag) | (res1 , seen1) | (_ , zero) with generateModelElement p seen1 section c dag
    generateEdges p seen section (e ∷ xs) (c & dag) | (res1 , seen1) | (_ , zero) | (res2 , seen2) = (concatenateTwoList res1 res2 , seen2)
    generateEdges p seen section (e ∷ xs) (c & dag) | (res1 , seen1) | (me , (suc m)) with generateEdges p seen1 section ((me , m) ∷ []) dag
    generateEdges p seen section (e ∷ xs) (c & dag) | (res1 , seen1) | (me , (suc m)) | (res2 , seen2) = (concatenateTwoList res1 res2 , seen2)

    generateIdentifierEdge : ∀ {n} -> Project -> List (ModelElement × Fin n) -> ℕ -> ModelDAG n -> String
    generateIdentifierEdge p es n dag with getElementAtIndex es n
    ... | nothing = ""
    ... | just e with generateEdges p [] Identifier (e ∷ []) dag
    ... | (x ∷ [] , _) = x
    ... | _ = ""
    
    generateIdentifierContext : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> String
    generateIdentifierContext p c dag with generateModelElement p [] Identifier c dag
    ... | (x ∷ [] , _) = x
    ... | _ = ""

    generateModelElement : ∀ {n} -> Project -> List ModelElement -> CodeSection -> Context ModelElement ModelElement n -> ModelDAG n -> (List String) × (List ModelElement)
    generateModelElement p seen Identifier (context me edges) dag = ((getModelElementName me) ∷ [] , seen)
    generateModelElement p seen Main (context me edges) dag with containsModelElement seen me
    ... | true = ([] , seen)
    ... | false with generateEdges p seen Main edges dag
    ... | (res , seen1) with me
    ... | (OutputInstance _ _) = ((concatenateStrings ((generateIdentifierContext p (context me edges) dag) ∷ " = " ∷
                                  (generateIdentifierEdge p edges 0 dag) ∷ ";" ∷ []))
                                        ∷ res , me ∷ seen1)
    ... | (Addition _) = ((concatenateStrings ((generateIdentifierContext p (context me edges) dag) ∷ " = " ∷
                                  (generateIdentifierEdge p edges 0 dag) ∷ " + " ∷ (generateIdentifierEdge p edges 1 dag) ∷ ";" ∷ []))
                                        ∷ res , me ∷ seen1)
    ... | (Multiplication _) = ((concatenateStrings ((generateIdentifierContext p (context me edges) dag) ∷ " = " ∷
                                  (generateIdentifierEdge p edges 0 dag) ∷ " * " ∷ (generateIdentifierEdge p edges 1 dag) ∷ ";" ∷ []))
                                        ∷ res , me ∷ seen1)
    ... | (InputInstance _ _) = (res , me ∷ seen1)
    ... | _ = ([] , seen)

generateModelElements : ∀ {n} -> Project -> List ModelElement -> ModelDAG n -> (List String) × (List ModelElement)
generateModelElements _ seen ∅ = ([] , seen)
generateModelElements p seen ((context me edges) & dag) with containsModelElement seen me
generateModelElements p seen (c & dag) | true = generateModelElements p seen dag
generateModelElements p seen (c & dag) | false with generateModelElement p seen Main c dag
...                                         | (res1 , seen1) with generateModelElements p seen1 dag
...                                         | (res2 , seen2) = (concatenateTwoList (Data.List.reverse res1) res2 , seen2)

collectEndModelElements : List ModelElement -> List ModelElement
collectEndModelElements [] = []
collectEndModelElements (m ∷ ms) with m
... | (OutputInstance _ _) = m ∷ collectEndModelElements ms
... | _ = collectEndModelElements ms

generateModel : Project -> Model -> List String
generateModel p (Operation n ins outs sms) with (createDAG (Operation n ins outs sms))
... | nothing = []
... | just dag with generateModelElements p [] dag
... | (res , _) = res

generateCode : Project -> String -> Bool × (List String)
generateCode p n with findModelInProjectWithName p n
... | nothing = false , concatenateStrings ("Could not find the root model " ∷ n ∷ []) ∷ []
... | just m = true , generateModel p m

checkAndGenerateCode : Maybe Project -> String -> Bool × (List String)
checkAndGenerateCode p n with checkProject p | p
... | true , _ | just pro = (generateCode pro n)
... | result | _ = result

denemeGen : List String
denemeGen = generateModel (project "" [] [] [] []) doubleOutputModel

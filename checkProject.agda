{-# OPTIONS --safe #-}

module checkProject where

open import utility
open import IMODEDataTypes
open import IMODEScannedDataTypes
open import createNodes

open import Data.Bool
open import Data.String
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Nat

checkStructureDefElem : String -> String × Type -> List String
checkStructureDefElem n (l , iNull) = concatenateStrings ("Type " ∷ n ∷ " label " ∷ l ∷ " is null." ∷ []) ∷ []
checkStructureDefElem _ _ = []

checkStructureDefElems : String -> List (String × Type) -> List String
checkStructureDefElems _ [] = []
checkStructureDefElems n (lt ∷ xs) = concatenateTwoList (checkStructureDefElem n lt) (checkStructureDefElems n xs)

checkType : Type -> List String
checkType (iUserDefined n iNull) = concatenateStrings ("Type " ∷ n ∷ " is null." ∷ []) ∷ []
checkType (iStructure n defElems) = checkStructureDefElems n defElems
checkType (iArray n ds iNull) = concatenateStrings ("Type " ∷ n ∷ " element type is null." ∷ []) ∷ []
checkType _ = []

checkTypes : List Type -> List String
checkTypes [] = []
checkTypes (t ∷ ts) = concatenateTwoList (checkType t) (checkTypes ts)

collectOutConIds : List (ℕ × String) -> List String
collectOutConIds [] = []
collectOutConIds ((n , id) ∷ xs) = id ∷ collectOutConIds xs

checkModelElement : ModelElement -> List String
checkModelElement m with getBaseModelProperties m
... | just (Properties n id inCons outCons) with contains inCons "" | contains (collectOutConIds outCons) ""
... | false | false = []
... | _ | _ = concatenateStrings ("There is an unconnected point in " ∷ n ∷ []) ∷ []
checkModelElement m | nothing = []

checkModelElements : List ModelElement -> List String
checkModelElements [] = []
checkModelElements (m ∷ ms) = concatenateTwoList (checkModelElement m) (checkModelElements ms)


checkModel : Model -> List String
checkModel (Operation n inputs outputs subModels) = checkModelElements (concatenate (inputs ∷ outputs ∷ subModels ∷ []))
checkModel _ = []

checkModels : List Model -> List String
checkModels [] = []
checkModels (m ∷ ms) = concatenateTwoList (checkModel m) (checkModels ms)


checkProject : Maybe Project -> Bool × (List String)
checkProject nothing = false , ("Project load failed." ∷ [])
checkProject (just (record {subModels = sms ; types = ts})) with checkTypes ts | checkModels sms
... | [] | [] = true , []
... | tErrors | mErrors = false , (concatenate (tErrors ∷ mErrors ∷ []))

containsModelElement : List ModelElement -> ModelElement -> Bool
containsModelElement [] _ = false
containsModelElement (m1 ∷ ms) m2 with (getModelElementID m1) == (getModelElementID m2)
... | true = true
... | false = containsModelElement ms m2

mutual
    checkForCyclicMulti : ∀ {n} -> List (ModelTree n) -> List ModelElement -> Bool × (List String)
    checkForCyclicMulti [] _ = true , []
    checkForCyclicMulti (t ∷ ts) seen with checkForCyclic t seen
    ... | false , errs = false , errs
    ... | true , _ = checkForCyclicMulti ts seen

    checkForCyclic : ∀ {n} -> ModelTree n -> List ModelElement -> Bool × (List String)
    checkForCyclic (ExampleTree a) _ = false , "ExampleTree" ∷ []
    checkForCyclic (Leaf _) _ = true , []
    checkForCyclic (Root ts) seen = checkForCyclicMulti ts seen
    checkForCyclic (m ∷ ts) seen with containsModelElement seen m
    ... | true = false , ("Cycle detected." ∷ [])
    ... | false = checkForCyclicMulti ts (m ∷ seen)

checkModelTree : ∀ {n} -> ModelTree n -> Bool × (List String)
checkModelTree t = checkForCyclic t [] 

deneme : Bool × (List String)
deneme with createModelTree exampleModel
... | nothing = false , ("Could not create tree." ∷ [])
... | just ts = checkForCyclic ts []
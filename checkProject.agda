{-# OPTIONS --safe #-}

module checkProject where

open import Data.Bool
open import Data.String
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Nat
open import IMODEDataTypes
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary.Decidable



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

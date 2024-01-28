{-# OPTIONS --safe #-}

module checkProject where

open import utility
open import IMODEDataTypes
open import ModelDAG
open import createDAG

open import Data.Bool
open import Data.String
open import Data.List hiding (_++_)
open import Data.Maybe
open import Data.Product
open import Data.Nat

data CheckResult : Set where
    Success : CheckResult
    Error : List String -> CheckResult

checkStructureDefElem : String -> String × Type -> List String
checkStructureDefElem n (l , iNull) = ("Type " ++ n ++ " label " ++ l ++ " is null.") ∷ []
checkStructureDefElem _ _ = []

checkStructureDefElems : String -> List (String × Type) -> List String
checkStructureDefElems _ [] = []
checkStructureDefElems n (lt ∷ xs) = concatenateTwoList (checkStructureDefElem n lt) (checkStructureDefElems n xs)

checkType : Type -> List String
checkType (iUserDefined n iNull) = ("Type " ++ n ++ " is null.") ∷ []
checkType (iStructure n defElems) = checkStructureDefElems n defElems
checkType (iArray n ds iNull) = ("Type " ++ n ++ " element type is null.") ∷ []
checkType _ = []

checkTypes : List Type -> List String
checkTypes [] = []
checkTypes (t ∷ ts) = concatenateTwoList (checkType t) (checkTypes ts)

collectOutConIds : List (ℕ × String) -> List String
collectOutConIds [] = []
collectOutConIds ((n , id) ∷ xs) = id ∷ collectOutConIds xs


checkInputConnectionCounts : ModelElement -> Bool
checkInputConnectionCounts (InputInstance (Properties _ _ inCons _) _) = (Data.List.length inCons) ==ℕ 0
checkInputConnectionCounts (OutputInstance (Properties _ _ inCons _) _) = (Data.List.length inCons) ==ℕ 1
checkInputConnectionCounts (Addition (Properties _ _ inCons _)) = (Data.List.length inCons) >=ℕ 2
checkInputConnectionCounts (Modulo (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (Multiplication (Properties _ _ inCons _)) = (Data.List.length inCons) >=ℕ 2
checkInputConnectionCounts (NumericCast (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 1
checkInputConnectionCounts (PolymorphicDivision (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (Subtraction (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (UnaryMinus (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 1
checkInputConnectionCounts (LogicalAnd (Properties _ _ inCons _)) = (Data.List.length inCons) >=ℕ 2
checkInputConnectionCounts (LogicalNor (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (LogicalNot (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 1
checkInputConnectionCounts (LogicalOr (Properties _ _ inCons _)) = (Data.List.length inCons) >=ℕ 2
checkInputConnectionCounts (LogicalSharp (Properties _ _ inCons _)) = (Data.List.length inCons) >=ℕ 2
checkInputConnectionCounts (LogicalXor (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (BitwiseAnd (Properties _ _ inCons _)) = (Data.List.length inCons) >=ℕ 2
checkInputConnectionCounts (BitwiseNot (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 1
checkInputConnectionCounts (BitwiseOr (Properties _ _ inCons _)) = (Data.List.length inCons) >=ℕ 2
checkInputConnectionCounts (BitwiseXor (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (LeftShift (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (RightShift (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (Different (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (Equal (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (GreaterThanEqual (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (LessThanEqual (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (StrictlyGreaterThan (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts (StrictlyLessThan (Properties _ _ inCons _)) = (Data.List.length inCons) ==ℕ 2
checkInputConnectionCounts _ = false


checkOutputConnectionCounts : ModelElement -> Bool
checkOutputConnectionCounts (InputInstance (Properties _ _ _ outCons) _) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (OutputInstance (Properties _ _ _ outCons) _) = (Data.List.length outCons) ==ℕ 0
checkOutputConnectionCounts (Addition (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (Modulo (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (Multiplication (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (NumericCast (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (PolymorphicDivision (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (Subtraction (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (UnaryMinus (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (LogicalAnd (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (LogicalNor (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (LogicalNot (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (LogicalOr (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (LogicalSharp (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (LogicalXor (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (BitwiseAnd (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (BitwiseNot (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (BitwiseOr (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (BitwiseXor (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (LeftShift (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (RightShift (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (Different (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (Equal (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (GreaterThanEqual (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (LessThanEqual (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (StrictlyGreaterThan (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts (StrictlyLessThan (Properties _ _ _ outCons)) = (Data.List.length outCons) ==ℕ 1
checkOutputConnectionCounts _ = false

checkInputConnections : ModelElement -> List String
checkInputConnections m with getBaseModelProperties m
... | nothing = []
... | just (Properties n id inCons outCons) with checkInputConnectionCounts m
... | false = ("Input connection count is not correct for " ++ n) ∷ []
... | true with contains inCons ""
... | false = []
... | true = ("There is an unconnected input point in " ++ n) ∷ []

checkOutputConnections : ModelElement -> List String
checkOutputConnections m with getBaseModelProperties m
... | nothing = []
... | just (Properties n id inCons outCons) with checkOutputConnectionCounts m
... | false = ("Output connection count is not correct for " ++ n) ∷ []
... | true with contains (collectOutConIds outCons) ""
... | false = []
... | true = ("There is an unconnected output point in " ++ n) ∷ []

checkModelElementsConnections : List ModelElement -> List String
checkModelElementsConnections [] = []
checkModelElementsConnections (m ∷ ms) = concatenate ((checkInputConnections m) ∷ (checkOutputConnections m) ∷ (checkModelElementsConnections ms) ∷ [])

-- Returns true if cyclic
checkForCyclic : ∀ {n} -> ModelDAG n -> Bool
checkForCyclic dag = containsDuplicateModelElement (DAGToList dag)

checkModelDAG : ∀ {n} -> Model -> ModelDAG n -> List String
checkModelDAG (Operation n inputs outputs subModels) dag with checkForCyclic dag
... | true = ("There is a cycle in " ++ n) ∷ []
... | false = []

checkModel : Model -> List String
checkModel (Operation n inputs outputs subModels) with checkModelElementsConnections (concatenate (inputs ∷ outputs ∷ subModels ∷ []))
checkModel (Operation n inputs outputs subModels) | [] with createDAG (Operation n inputs outputs subModels)
checkModel (Operation n inputs outputs subModels) | [] | nothing = ("Could not create DAG for " ++ n) ∷ []
checkModel m                                      | [] | just dag = checkModelDAG m dag
checkModel (Operation n inputs outputs subModels) | l = l

checkModels : List Model -> List String
checkModels [] = []
checkModels (m ∷ ms) = concatenateTwoList (checkModel m) (checkModels ms)

checkProject : Maybe Project -> CheckResult
checkProject nothing = Error ("Project load failed." ∷ [])
checkProject (just (record {subModels = sms ; types = ts})) with checkTypes ts | checkModels sms
... | [] | [] = Success
... | tErrors | mErrors = Error (concatenate (tErrors ∷ mErrors ∷ []))

deneme : List String
deneme = checkModel exampleModel

deneme2 : List String
deneme2 = checkModel exampleModelThatHasCycle

deneme3 : List String
deneme3 = checkModel exampleModelThatHasCycle2

deneme4 : List String
deneme4 = checkModel doubleOutputModel
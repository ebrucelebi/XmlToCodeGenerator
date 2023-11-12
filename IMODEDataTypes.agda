{-# OPTIONS --safe #-}
module IMODEDataTypes where

open import Data.String
open import Data.List
open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.Maybe
open import Relation.Nullary.Decidable

data Type : Set where
  iNone : Type
  iNull : Type
  iBool : Type
  iChar : Type
  iInt8 : Type
  iInt16 : Type
  iInt32 : Type
  iInt64 : Type
  iUInt8 : Type
  iUInt16 : Type
  iUInt32 : Type
  iUInt64 : Type
  iFloat32 : Type
  iFloat64 : Type
  iStructure : (name : String) -> List (String × Type) -> Type
  iArray : (name : String) -> List (ℕ) -> Type -> Type
  iEnum : (name : String) -> (values : List String) -> Type
  iUserDefined : (name : String) -> Type -> Type
  iOther : (otherTypesName : String) -> Type

getType : String -> Type
getType "_null" = iNull
getType "bool" = iBool
getType "char" = iChar
getType "int8" = iInt8
getType "int16" = iInt16
getType "int32" = iInt32
getType "int64" = iInt64
getType "uint8" = iUInt8
getType "uint16" = iUInt16
getType "uint32" = iUInt32
getType "uint64" = iUInt64
getType "float32" = iFloat32
getType "float64" = iFloat64
getType _ = iNone

data IOType : Set where
  IO_None : IOType
  Input : IOType
  Output : IOType
  InputOutput : IOType

getIOType : String -> IOType
getIOType "0" = Input
getIOType "1" = Output
getIOType "2" = InputOutput
getIOType _ = IO_None

record Interface : Set where
  field
    name : String
    type : Type
    ioType : IOType
    value : String
    comment : String

record Constant : Set where
  field
    name : String
    type : Type
    value : String
    comment : String

data BaseModelElementProperties : Set where
  Properties : (name : String) -> (id : String) -> (inputConsId : List String) -> (outputConsId : List (ℕ × String)) -> BaseModelElementProperties

data ModelElement : Set where
  TestModelElement : ℕ -> ModelElement
  Connection : String -> (id : String) -> (startModelId : String) -> (endModelId : String) -> ModelElement
  Input : String -> (id : String) -> Type -> ModelElement
  Output : String -> (id : String) -> Type -> ModelElement
  InputInstance : BaseModelElementProperties -> (sourceId : String) -> ModelElement
  OutputInstance : BaseModelElementProperties -> (sourceId : String) -> ModelElement
  Addition : BaseModelElementProperties -> ModelElement
  Modulo : BaseModelElementProperties -> ModelElement
  Multiplication : BaseModelElementProperties -> ModelElement
  NumericCast : BaseModelElementProperties -> ModelElement
  PolymorphicDivision : BaseModelElementProperties -> ModelElement
  Subtraction : BaseModelElementProperties -> ModelElement
  UnaryMinus : BaseModelElementProperties -> ModelElement
  LogicalAnd : BaseModelElementProperties -> ModelElement
  LogicalNor : BaseModelElementProperties -> ModelElement
  LogicalNot : BaseModelElementProperties -> ModelElement
  LogicalOr : BaseModelElementProperties -> ModelElement
  LogicalSharp : BaseModelElementProperties -> ModelElement
  LogicalXor : BaseModelElementProperties -> ModelElement
  BitwiseAnd : BaseModelElementProperties -> ModelElement
  BitwiseNot : BaseModelElementProperties -> ModelElement
  BitwiseOr : BaseModelElementProperties -> ModelElement
  BitwiseXor : BaseModelElementProperties -> ModelElement
  LeftShift : BaseModelElementProperties -> ModelElement
  RightShift : BaseModelElementProperties -> ModelElement
  Different : BaseModelElementProperties -> ModelElement
  Equal : BaseModelElementProperties -> ModelElement
  GreaterThanEqual : BaseModelElementProperties -> ModelElement
  LessThanEqual : BaseModelElementProperties -> ModelElement
  StrictlyGreaterThan : BaseModelElementProperties -> ModelElement
  StrictlyLessThan : BaseModelElementProperties -> ModelElement

data Model : Set where
  TestModel : ℕ -> Model
  Operation : String -> (inputs : List ModelElement) -> (outputs : List ModelElement) -> (subModels : List ModelElement)-> Model
  
record Project : Set where
  field
    name : String
    subModels : List Model
    types : List Type
    interfaces : List Interface
    constants : List Constant

contains : List String -> String -> Bool
contains [] _ = false
contains (x ∷ xs) y with isYes (x Data.String.≟ y)
... | true = true
... | false = contains xs y

concatenate : ∀{ℓ}{A : Set ℓ} → List (List A) → List A
concatenate [] = []
concatenate (x ∷ xs) = x Data.List.++ concatenate xs

concatenateTwoList : ∀{ℓ}{A : Set ℓ} → List A -> List A → List A
concatenateTwoList xs1 xs2 = xs1 Data.List.++ xs2


concatenateStrings : List String -> String
concatenateStrings [] = ""
concatenateStrings (x ∷ xs) = x Data.String.++ (concatenateStrings xs)

getBaseModelProperties : ModelElement -> Maybe BaseModelElementProperties
getBaseModelProperties (InputInstance p _) = just p
getBaseModelProperties (OutputInstance p _) = just p
getBaseModelProperties (Addition p) = just p
getBaseModelProperties (Modulo p) = just p
getBaseModelProperties (Multiplication p) = just p
getBaseModelProperties (NumericCast p) = just p
getBaseModelProperties (PolymorphicDivision p) = just p
getBaseModelProperties (Subtraction p) = just p
getBaseModelProperties (UnaryMinus p) = just p
getBaseModelProperties (LogicalAnd p) = just p
getBaseModelProperties (LogicalNor p) = just p
getBaseModelProperties (LogicalNot p) = just p
getBaseModelProperties (LogicalOr p) = just p
getBaseModelProperties (LogicalSharp p) = just p
getBaseModelProperties (LogicalXor p) = just p
getBaseModelProperties (BitwiseAnd p) = just p
getBaseModelProperties (BitwiseNot p) = just p
getBaseModelProperties (BitwiseOr p) = just p
getBaseModelProperties (BitwiseXor p) = just p
getBaseModelProperties (LeftShift p) = just p
getBaseModelProperties (RightShift p) = just p
getBaseModelProperties (Different p) = just p
getBaseModelProperties (Equal p) = just p
getBaseModelProperties (GreaterThanEqual p) = just p
getBaseModelProperties (LessThanEqual p) = just p
getBaseModelProperties (StrictlyGreaterThan p) = just p
getBaseModelProperties (StrictlyLessThan p) = just p
getBaseModelProperties _ = nothing

getModelElementID : ModelElement -> String
getModelElementID m with getBaseModelProperties m
... | just (Properties _ id _ _) = id
... | _ with m
... | Input _ id _ = id 
... | Output _ id _ = id
... | Connection _ id _ _ = id
... | _ = "" -- Should not come here

findModelElementWithID : List ModelElement -> String -> Maybe ModelElement
findModelElementWithID [] _ = nothing
findModelElementWithID (m ∷ ms) otherId with isYes ((getModelElementID m) Data.String.≟ otherId)
... | true = just m
... | false = findModelElementWithID ms otherId

findModelElementInModelWithID : Model -> String -> Maybe ModelElement
findModelElementInModelWithID (Operation _ inputs outputs subModels) id = findModelElementWithID (concatenate (inputs ∷ outputs ∷ subModels ∷ [])) id
findModelElementInModelWithID _ _ = nothing

findModelElementInModelListWithID : List Model -> String -> Maybe ModelElement
findModelElementInModelListWithID [] _ = nothing
findModelElementInModelListWithID (m ∷ ms) id with findModelElementInModelWithID m id
... | just me = just me
... | nothing = findModelElementInModelListWithID ms id

findModelElementInProjectWithID : Project -> String -> Maybe ModelElement
findModelElementInProjectWithID record {subModels = sms} id = findModelElementInModelListWithID sms id


findModelInModelListWithName : List Model -> String -> Maybe Model
findModelInModelListWithName [] _ = nothing
findModelInModelListWithName ((Operation n1 _ _ _) ∷ ms) n2 with isYes (n1 Data.String.≟ n2)
findModelInModelListWithName ((Operation n1 _ _ _) ∷ ms) n2 | false = findModelInModelListWithName ms n2
findModelInModelListWithName (m ∷ ms) n2 | true = just m
findModelInModelListWithName (m ∷ ms) n2 = findModelInModelListWithName ms n2

findModelInProjectWithName : Project -> String -> Maybe Model
findModelInProjectWithName record {subModels = sms} n = findModelInModelListWithName sms n 

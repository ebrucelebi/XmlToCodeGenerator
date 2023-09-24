module IMODEDataTypes where

open import Data.String
open import Data.List
open import Data.Bool
open import Data.Product
open import Data.Nat

data Type : Set where
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
  iOther : (name : String) -> Type -> Type
  
data IOType : Set where
  Input : IOType
  Output : IOType
  InputOutput : IOType

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
    
data Model : Set where
  Connection : String -> (startModel : Model) -> (endModel : Model) -> Model
  Input : String -> Type -> Model
  Output : String -> Type -> Model
  Addition : String -> (inputs : List Model) -> Model

data Frame : Set where
  Operation : String -> (inputs : List Model) -> (outputs : List Model) -> Frame
  
record Project : Set where
  constructor emptyProject
  field
    name : String
    subModels : List Frame
    types : List Type
    interfaces : List Interface
    constants : List Constant

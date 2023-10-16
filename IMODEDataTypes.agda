module IMODEDataTypes where

open import Data.String
open import Data.List
open import Data.Bool
open import Data.Product
open import Data.Nat

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
  Properties : (name : String) -> (id : String) -> (inputConsId : List String) -> BaseModelElementProperties

data ModelElement : Set where
  TestModelElement : ℕ -> ModelElement
  Connection : String -> (id : String) -> (startModelId : String) -> (endModelId : String) -> ModelElement
  Input : String -> (id : String) -> Type -> ModelElement
  Output : String -> (id : String) -> Type -> ModelElement
  InputInstance :  String -> (id : String) -> (sourceId : String) -> ModelElement
  OutputInstance : String -> (id : String) -> (sourceId : String) -> (inputConsId : List String) -> ModelElement
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


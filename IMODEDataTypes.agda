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

data Model : Set where
  TestModel : ℕ -> Model
  Connection : String -> (id : String) -> (startModelId : String) -> (endModelId : String) -> Model
  Input : String -> (id : String) -> Type -> Model
  Output : String -> (id : String) -> Type -> Model
  InputInstance :  String -> (id : String) -> (sourceId : String) -> Model
  OutputInstance : String -> (id : String) -> (sourceId : String) -> (inputConsId : List String) -> Model
  Addition : BaseModelElementProperties -> Model
  Modulo : BaseModelElementProperties -> Model
  Multiplication : BaseModelElementProperties -> Model
  NumericCast : BaseModelElementProperties -> Model
  PolymorphicDivision : BaseModelElementProperties -> Model
  Subtraction : BaseModelElementProperties -> Model
  UnaryMinus : BaseModelElementProperties -> Model
  LogicalAnd : BaseModelElementProperties -> Model
  LogicalNor : BaseModelElementProperties -> Model
  LogicalNot : BaseModelElementProperties -> Model
  LogicalOr : BaseModelElementProperties -> Model
  LogicalSharp : BaseModelElementProperties -> Model
  LogicalXor : BaseModelElementProperties -> Model
  BitwiseAnd : BaseModelElementProperties -> Model
  BitwiseNot : BaseModelElementProperties -> Model
  BitwiseOr : BaseModelElementProperties -> Model
  BitwiseXor : BaseModelElementProperties -> Model
  LeftShift : BaseModelElementProperties -> Model
  RightShift : BaseModelElementProperties -> Model
  Different : BaseModelElementProperties -> Model
  Equal : BaseModelElementProperties -> Model
  GreaterThanEqual : BaseModelElementProperties -> Model
  LessThanEqual : BaseModelElementProperties -> Model
  StrictlyGreaterThan : BaseModelElementProperties -> Model
  StrictlyLessThan : BaseModelElementProperties -> Model

data Frame : Set where
  Operation : String -> (inputs : List Model) -> (outputs : List Model) -> (subModels : List Model)-> Frame
  
record Project : Set where
  field
    name : String
    subModels : List Frame
    types : List Type
    interfaces : List Interface
    constants : List Constant


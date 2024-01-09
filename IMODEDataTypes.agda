{-# OPTIONS --safe #-}

module IMODEDataTypes where

open import utility

open import Data.String
open import Data.List
open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.Maybe

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
  Operation : String -> (inputs : List ModelElement) -> (outputs : List ModelElement) -> (subModels : List ModelElement)-> Model
  
record Project : Set where
  constructor project
  field
    name : String
    subModels : List Model
    types : List Type
    interfaces : List Interface
    constants : List Constant

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

getModelElementName : ModelElement -> String
getModelElementName m with getBaseModelProperties m
... | just (Properties n _ _ _) = n
... | _ with m
... | Input n _ _ = n 
... | Output n _ _ = n
... | Connection n _ _ _ = n
... | _ = "" -- Should not come here

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
findModelElementWithID (m ∷ ms) otherId with (getModelElementID m) == otherId
... | true = just m
... | false = findModelElementWithID ms otherId

findModelElementInModelWithID : Model -> String -> Maybe ModelElement
findModelElementInModelWithID (Operation _ inputs outputs subModels) id = findModelElementWithID (concatenate (inputs ∷ outputs ∷ subModels ∷ [])) id

findModelElementsInModelWithID : Model -> List String -> Maybe (List ModelElement)
findModelElementsInModelWithID _ [] = just []
findModelElementsInModelWithID m (x ∷ xs) with findModelElementInModelWithID m x | findModelElementsInModelWithID m xs
... | just me | just mes = just (me ∷ mes)
... | _ | _ = nothing

findModelElementInModelListWithID : List Model -> String -> Maybe ModelElement
findModelElementInModelListWithID [] _ = nothing
findModelElementInModelListWithID (m ∷ ms) id with findModelElementInModelWithID m id
... | just me = just me
... | nothing = findModelElementInModelListWithID ms id

findModelElementInProjectWithID : Project -> String -> Maybe ModelElement
findModelElementInProjectWithID record {subModels = sms} id = findModelElementInModelListWithID sms id

findModelInModelListWithName : List Model -> String -> Maybe Model
findModelInModelListWithName [] _ = nothing
findModelInModelListWithName ((Operation n1 _ _ _) ∷ ms) n2 with n1 == n2
findModelInModelListWithName ((Operation n1 _ _ _) ∷ ms) n2 | false = findModelInModelListWithName ms n2
findModelInModelListWithName (m ∷ ms) n2 | true = just m

findModelInProjectWithName : Project -> String -> Maybe Model
findModelInProjectWithName record {subModels = sms} n = findModelInModelListWithName sms n 

findEndModels : List ModelElement -> List ModelElement
findEndModels [] = []
findEndModels (x ∷ xs) with getBaseModelProperties x
... | just (Properties _ _ _ []) = x ∷ findEndModels xs
... | _ = findEndModels xs

findNonConnectionModelElementCountAlt : List ModelElement -> ℕ
findNonConnectionModelElementCountAlt [] = zero
findNonConnectionModelElementCountAlt ((Connection _ _ _ _) ∷ xs) = findNonConnectionModelElementCountAlt xs
findNonConnectionModelElementCountAlt (x ∷ xs) = suc (findNonConnectionModelElementCountAlt xs)

findNonConnectionModelElementCount : Model -> ℕ
findNonConnectionModelElementCount (Operation _ _ _ sm) = findNonConnectionModelElementCountAlt sm

containsModelElement : List ModelElement -> ModelElement -> Bool
containsModelElement [] _ = false
containsModelElement (m1 ∷ ms) m2 with (getModelElementID m1) == (getModelElementID m2)
... | true = true
... | false = containsModelElement ms m2

containsDuplicateModelElement : List ModelElement -> Bool
containsDuplicateModelElement [] = false
containsDuplicateModelElement (m ∷ ms) = (containsModelElement ms m) ∨ (containsDuplicateModelElement ms)

appendUniqueModelElement : List ModelElement -> List ModelElement -> List ModelElement
appendUniqueModelElement [] l = l
appendUniqueModelElement l [] = l
appendUniqueModelElement (x ∷ xs) l with containsModelElement (appendUniqueModelElement xs l) x
... | true = (appendUniqueModelElement xs l)
... | false = x ∷ (appendUniqueModelElement xs l)

exampleModel : Model
exampleModel = (Operation "logicModel1"
 (Input "Input1" "1696681110711_2" iInt16 ∷
  Input "Input3" "1696681112176_4" iInt16 ∷ [])
 (Output "Output1" "1696681118077_2" iInt16 ∷ [])
 (InputInstance
  (Properties "Input1" "1696681110644_1" []
   ((0 , "1696681114575_1") ∷ []))
  "1696681110711_2"
  ∷
  InputInstance
  (Properties "Input3" "1696681112129_3" []
   ((0 , "1696681115337_2") ∷ []))
  "1696681112176_4"
  ∷
  Addition
  (Properties "Addition1" "1696681114187_1"
   ("1696681114575_1" ∷ "1696681115337_2" ∷ [])
   ((0 , "1696681118357_3") ∷ []))
  ∷
  Connection "Connect1" "1696681114575_1" "1696681110644_1"
  "1696681114187_1"
  ∷
  Connection "Connect2" "1696681115337_2" "1696681112129_3"
  "1696681114187_1"
  ∷
  OutputInstance
  (Properties "Output1" "1696681118011_1" ("1696681118357_3" ∷ [])
   [])
  "1696681118077_2"
  ∷
  Connection "Connect3" "1696681118357_3" "1696681114187_1"
  "1696681118011_1"
  ∷ []))

exampleModelThatHasCycle : Model
exampleModelThatHasCycle = (Operation "hasCycle"
 (Input "Input7" "1702980090917_8" iInt16 ∷ [])
 (Output "Output5" "1702980105810_6" iInt16 ∷ [])
 (InputInstance
  (Properties "Input7" "1702980090841_7" []
   ((0 , "1702980106934_9") ∷ []))
  "1702980090917_8"
  ∷
  Addition
  (Properties "Addition3" "1702980093845_3"
   ("1702980106934_9" ∷ "1702980107873_10" ∷ [])
   ((0 , "1702980106161_8") ∷ (0 , "1702980107873_10") ∷ []))
  ∷
  OutputInstance
  (Properties "Output5" "1702980105745_5" ("1702980106161_8" ∷ [])
   [])
  "1702980105810_6"
  ∷
  Connection "Connect8" "1702980106161_8" "1702980093845_3"
  "1702980105745_5"
  ∷
  Connection "Connect9" "1702980106934_9" "1702980090841_7"
  "1702980093845_3"
  ∷
  Connection "Connect10" "1702980107873_10" "1702980093845_3"
  "1702980093845_3"
  ∷ []))

exampleModelThatHasCycle2 : Model
exampleModelThatHasCycle2 = (Operation "hasCycle2"
 (Input "Input9" "1702980358820_10" iInt16 ∷ [])
 (Output "Output7" "1702980363847_8" iInt16 ∷ [])
 (InputInstance
  (Properties "Input9" "1702980358768_9" []
   ((0 , "1702980381220_13") ∷ []))
  "1702980358820_10"
  ∷
  Addition
  (Properties "Addition4" "1702980359718_4"
   ("1702980381220_13" ∷ "1702980391184_15" ∷ [])
   ((0 , "1702980379810_12") ∷ (0 , "1702980388605_14") ∷ []))
  ∷
  Addition
  (Properties "Addition5" "1702980360884_5"
   ("1702980379810_12" ∷ "1702980388605_14" ∷ [])
   ((0 , "1702980364216_11") ∷ (0 , "1702980391184_15") ∷ []))
  ∷
  OutputInstance
  (Properties "Output7" "1702980363784_7" ("1702980364216_11" ∷ [])
   [])
  "1702980363847_8"
  ∷
  Connection "Connect11" "1702980364216_11" "1702980360884_5"
  "1702980363784_7"
  ∷
  Connection "Connect12" "1702980379810_12" "1702980359718_4"
  "1702980360884_5"
  ∷
  Connection "Connect13" "1702980381220_13" "1702980358768_9"
  "1702980359718_4"
  ∷
  Connection "Connect14" "1702980388605_14" "1702980359718_4"
  "1702980360884_5"
  ∷
  Connection "Connect15" "1702980391184_15" "1702980360884_5"
  "1702980359718_4"
  ∷ []))

doubleOutputModel : Model
doubleOutputModel = (Operation "doubleOutput"
 (Input "Input11" "1702982541890_12" iInt16 ∷
  Input "Input13" "1702982542944_14" iInt16 ∷ [])
 (Output "Output9" "1702982555602_10" iInt16 ∷
  Output "Output11" "1702982556952_12" iInt16 ∷ [])
 (InputInstance
  (Properties "Input11" "1702982541825_11" []
   ((0 , "1702982548262_16") ∷ []))
  "1702982541890_12"
  ∷
  InputInstance
  (Properties "Input13" "1702982542875_13" []
   ((0 , "1702982549172_17") ∷ (0 , "1702982551338_19") ∷ []))
  "1702982542944_14"
  ∷
  Addition
  (Properties "Addition6" "1702982544232_6"
   ("1702982548262_16" ∷ "1702982549172_17" ∷ [])
   ((0 , "1702982549830_18") ∷ (0 , "1702982558161_20") ∷ []))
  ∷
  Multiplication
  (Properties "Multiplication1" "1702982546543_1"
   ("1702982549830_18" ∷ "1702982551338_19" ∷ [])
   ((0 , "1702982559195_21") ∷ []))
  ∷
  Connection "Connect16" "1702982548262_16" "1702982541825_11"
  "1702982544232_6"
  ∷
  Connection "Connect17" "1702982549172_17" "1702982542875_13"
  "1702982544232_6"
  ∷
  Connection "Connect18" "1702982549830_18" "1702982544232_6"
  "1702982546543_1"
  ∷
  Connection "Connect19" "1702982551338_19" "1702982542875_13"
  "1702982546543_1"
  ∷
  OutputInstance
  (Properties "Output9" "1702982555559_9" ("1702982558161_20" ∷ [])
   [])
  "1702982555602_10"
  ∷
  OutputInstance
  (Properties "Output11" "1702982556907_11" ("1702982559195_21" ∷ [])
   [])
  "1702982556952_12"
  ∷
  Connection "Connect20" "1702982558161_20" "1702982544232_6"
  "1702982555559_9"
  ∷
  Connection "Connect21" "1702982559195_21" "1702982546543_1"
  "1702982556907_11"
  ∷ [])) 
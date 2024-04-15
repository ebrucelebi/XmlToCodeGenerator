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

getStringFromType : Type -> String
getStringFromType iNull = "_null"
getStringFromType iBool = "bool"
getStringFromType iChar = "char"
getStringFromType iInt8 = "int8"
getStringFromType iInt16 = "int16"
getStringFromType iInt32 = "int32"
getStringFromType iInt64 = "int64"
getStringFromType iUInt8 = "uint8"
getStringFromType iUInt16 = "uint16"
getStringFromType iUInt32 = "uint32"
getStringFromType iUInt64 = "uint64"
getStringFromType iFloat32 = "float32"
getStringFromType iFloat64 = "float64"
getStringFromType (iStructure n _)  = n
getStringFromType (iArray n _ _)  = n
getStringFromType (iEnum n _)  = n
getStringFromType (iUserDefined n _)  = n
getStringFromType _ = ""

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
  Properties :  (name : String) ->
                (id : String) ->
                (inputConsId : List String) ->
                (outputConsId : List (ℕ × String)) ->
                (condConsId : List String) ->
                (paramConsId : List String) ->
                BaseModelElementProperties

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
  If : BaseModelElementProperties -> ModelElement
  Previous : BaseModelElementProperties -> List String -> ModelElement
  Textual : BaseModelElementProperties -> String -> ModelElement

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
getBaseModelProperties (If p) = just p
getBaseModelProperties (Previous p _) = just p
getBaseModelProperties (Textual p _) = just p
getBaseModelProperties _ = nothing

getModelElementName : ModelElement -> String
getModelElementName m with getBaseModelProperties m
... | just (Properties n _ _ _ _ _) = n
... | _ with m
... | Input n _ _ = n 
... | Output n _ _ = n
... | Connection n _ _ _ = n
... | _ = "" -- Should not come here

getModelElementID : ModelElement -> String
getModelElementID m with getBaseModelProperties m
... | just (Properties _ id _ _ _ _) = id
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
findModelElementsInModelWithID m ("" ∷ xs) = findModelElementsInModelWithID m xs
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
... | just (Properties _ _ _ [] _ _) = x ∷ findEndModels xs
... | _ = findEndModels xs

findPreviousModels : List ModelElement -> List ModelElement
findPreviousModels [] = []
findPreviousModels ((Previous p v) ∷ xs) = (Previous p v) ∷ findPreviousModels xs
findPreviousModels (x ∷ xs) = findPreviousModels xs

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
   ((0 , "1696681114575_1") ∷ []) [] [])
  "1696681110711_2"
  ∷
  InputInstance
  (Properties "Input3" "1696681112129_3" []
   ((0 , "1696681115337_2") ∷ []) [] [])
  "1696681112176_4"
  ∷
  Addition
  (Properties "Addition1" "1696681114187_1"
   ("1696681114575_1" ∷ "1696681115337_2" ∷ [])
   ((0 , "1696681118357_3") ∷ []) [] [])
  ∷
  Connection "Connect1" "1696681114575_1" "1696681110644_1"
  "1696681114187_1"
  ∷
  Connection "Connect2" "1696681115337_2" "1696681112129_3"
  "1696681114187_1"
  ∷
  OutputInstance
  (Properties "Output1" "1696681118011_1" ("1696681118357_3" ∷ []) []
   [] [])
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
   ((0 , "1702980106934_9") ∷ []) [] [])
  "1702980090917_8"
  ∷
  Addition
  (Properties "Addition3" "1702980093845_3"
   ("1702980106934_9" ∷ "1702980107873_10" ∷ [])
   ((0 , "1702980106161_8") ∷ (0 , "1702980107873_10") ∷ []) [] [])
  ∷
  OutputInstance
  (Properties "Output5" "1702980105745_5" ("1702980106161_8" ∷ []) []
   [] [])
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
   ((0 , "1702980381220_13") ∷ []) [] [])
  "1702980358820_10"
  ∷
  Addition
  (Properties "Addition4" "1702980359718_4"
   ("1702980381220_13" ∷ "1702980391184_15" ∷ [])
   ((0 , "1702980379810_12") ∷ (0 , "1702980388605_14") ∷ []) [] [])
  ∷
  Addition
  (Properties "Addition5" "1702980360884_5"
   ("1702980379810_12" ∷ "1702980388605_14" ∷ [])
   ((0 , "1702980364216_11") ∷ (0 , "1702980391184_15") ∷ []) [] [])
  ∷
  OutputInstance
  (Properties "Output7" "1702980363784_7" ("1702980364216_11" ∷ [])
   [] [] [])
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
   ((0 , "1702982548262_16") ∷ []) [] [])
  "1702982541890_12"
  ∷
  InputInstance
  (Properties "Input13" "1702982542875_13" []
   ((0 , "1702982549172_17") ∷ (0 , "1702982551338_19") ∷ []) [] [])
  "1702982542944_14"
  ∷
  Addition
  (Properties "Addition6" "1702982544232_6"
   ("1702982548262_16" ∷ "1702982549172_17" ∷ [])
   ((0 , "1702982549830_18") ∷ (0 , "1702982558161_20") ∷ []) [] [])
  ∷
  Multiplication
  (Properties "Multiplication1" "1702982546543_1"
   ("1702982549830_18" ∷ "1702982551338_19" ∷ [])
   ((0 , "1702982559195_21") ∷ []) [] [])
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
   [] [] [])
  "1702982555602_10"
  ∷
  OutputInstance
  (Properties "Output11" "1702982556907_11" ("1702982559195_21" ∷ [])
   [] [] [])
  "1702982556952_12"
  ∷
  Connection "Connect20" "1702982558161_20" "1702982544232_6"
  "1702982555559_9"
  ∷
  Connection "Connect21" "1702982559195_21" "1702982546543_1"
  "1702982556907_11"
  ∷ []))

ifExample : Model
ifExample = (Operation "ifExample"
 (Input "Input1" "1710592239485_16" iInt16 ∷
  Input "Input2" "1710592245120_18" iInt16 ∷ [])
 (Output "Output" "1710592289986_12" iInt16 ∷ [])
 (InputInstance
  (Properties "Input1" "1710592239427_15" []
   ((0 , "1710592252981_21") ∷ []) [] [])
  "1710592239485_16"
  ∷
  InputInstance
  (Properties "Input2" "1710592245044_17" []
   ((0 , "1710592253797_22") ∷ []) [] [])
  "1710592245120_18"
  ∷
  StrictlyGreaterThan
  (Properties "StrictlyGreaterThan1" "1710592252194_1"
   ("1710592252981_21" ∷ "1710592253797_22" ∷ [])
   ((0 , "1710592256880_23") ∷ []) [] [])
  ∷
  Connection "Connect21" "1710592252981_21" "1710592239427_15"
  "1710592252194_1"
  ∷
  Connection "Connect22" "1710592253797_22" "1710592245044_17"
  "1710592252194_1"
  ∷
  If
  (Properties "If1" "1710592255112_1"
   ("1710592281009_29" ∷ "1710592275621_26" ∷ [])
   ((0 , "1710592290399_30") ∷ []) ("1710592256880_23" ∷ []) [])
  ∷
  Connection "Connect23" "1710592256880_23" "1710592252194_1"
  "1710592255112_1"
  ∷
  InputInstance
  (Properties "Input1" "1710592265198_19" []
   ((0 , "1710592279296_27") ∷ []) [] [])
  "1710592239485_16"
  ∷
  InputInstance
  (Properties "Input2" "1710592266085_20" []
   ((0 , "1710592279930_28") ∷ []) [] [])
  "1710592245120_18"
  ∷
  Addition
  (Properties "Addition6" "1710592268194_6"
   ("1710592273829_24" ∷ "1710592274553_25" ∷ [])
   ((0 , "1710592275621_26") ∷ []) [] [])
  ∷
  InputInstance
  (Properties "Input1" "1710592272301_21" []
   ((0 , "1710592273829_24") ∷ []) [] [])
  "1710592239485_16"
  ∷
  InputInstance
  (Properties "Input2" "1710592273211_22" []
   ((0 , "1710592274553_25") ∷ []) [] [])
  "1710592245120_18"
  ∷
  Connection "Connect24" "1710592273829_24" "1710592272301_21"
  "1710592268194_6"
  ∷
  Connection "Connect25" "1710592274553_25" "1710592273211_22"
  "1710592268194_6"
  ∷
  Connection "Connect26" "1710592275621_26" "1710592268194_6"
  "1710592255112_1"
  ∷
  Subtraction
  (Properties "Subtraction1" "1710592278893_1"
   ("1710592279296_27" ∷ "1710592279930_28" ∷ [])
   ((0 , "1710592281009_29") ∷ []) [] [])
  ∷
  Connection "Connect27" "1710592279296_27" "1710592265198_19"
  "1710592278893_1"
  ∷
  Connection "Connect28" "1710592279930_28" "1710592266085_20"
  "1710592278893_1"
  ∷
  Connection "Connect29" "1710592281009_29" "1710592278893_1"
  "1710592255112_1"
  ∷
  OutputInstance
  (Properties "Output" "1710592289927_11"
   ("1710592290399_30" ∷ []) [] [] [])
  "1710592289986_12"
  ∷
  Connection "Connect30" "1710592290399_30" "1710592255112_1"
  "1710592289927_11"
  ∷ []))

ifExample2 : Model
ifExample2 = (Operation "ifExample2"
 (Input "Cond1" "1711548137505_36" iBool ∷
  Input "Cond2" "1711548139329_38" iBool ∷
  Input "Input1" "1711548140858_40" iInt16 ∷
  Input "Input2" "1711548142405_42" iInt16 ∷
  Input "Input3" "1711548144841_44" iInt16 ∷ [])
 (Output "Output" "1711548075521_13" iInt16 ∷ [])
 (If
  (Properties "If1" "1711548117930_3"
   ("1711548158236_46" ∷ "1711548157599_45" ∷ [])
   ((0 , "1711548153726_43") ∷ (0 , "1711548227433_56") ∷ [])
   ("1711548123135_41" ∷ []) [])
  ∷
  Connection "Connect41" "1711548123135_41" "1711548137457_35"
  "1711548117930_3"
  ∷
  If
  (Properties "If2" "1711548125723_4"
   ("1711548153726_43" ∷ "1711548155675_44" ∷ [])
   ((0 , "1711548225982_55") ∷ []) ("1711548152108_42" ∷ []) [])
  ∷
  InputInstance
  (Properties "Cond1" "1711548137457_35" []
   ((0 , "1711548123135_41") ∷ []) [] [])
  "1711548137505_36"
  ∷
  InputInstance
  (Properties "Cond2" "1711548139256_37" []
   ((0 , "1711548152108_42") ∷ []) [] [])
  "1711548139329_38"
  ∷
  InputInstance
  (Properties "Input1" "1711548140806_39" []
   ((0 , "1711548158236_46") ∷ []) [] [])
  "1711548140858_40"
  ∷
  InputInstance
  (Properties "Input2" "1711548142356_41" []
   ((0 , "1711548157599_45") ∷ []) [] [])
  "1711548142405_42"
  ∷
  InputInstance
  (Properties "Input3" "1711548144751_43" []
   ((0 , "1711548155675_44") ∷ []) [] [])
  "1711548144841_44"
  ∷
  Connection "Connect42" "1711548152108_42" "1711548139256_37"
  "1711548125723_4"
  ∷
  Connection "Connect43" "1711548153726_43" "1711548117930_3"
  "1711548125723_4"
  ∷
  Connection "Connect44" "1711548155675_44" "1711548144751_43"
  "1711548125723_4"
  ∷
  Connection "Connect45" "1711548157599_45" "1711548142356_41"
  "1711548117930_3"
  ∷
  Connection "Connect46" "1711548158236_46" "1711548140806_39"
  "1711548117930_3"
  ∷
  OutputInstance
  (Properties "Output" "1711548202968_17" ("1711548230844_57" ∷ [])
   [] [] [])
  "1711548075521_13"
  ∷
  Addition
  (Properties "Addition8" "1711548224252_8"
   ("1711548227433_56" ∷ "1711548225982_55" ∷ [])
   ((0 , "1711548230844_57") ∷ []) [] [])
  ∷
  Connection "Connect55" "1711548225982_55" "1711548125723_4"
  "1711548224252_8"
  ∷
  Connection "Connect56" "1711548227433_56" "1711548117930_3"
  "1711548224252_8"
  ∷
  Connection "Connect57" "1711548230844_57" "1711548224252_8"
  "1711548202968_17"
  ∷ []))
  
ifExample3 : Model
ifExample3 = (Operation "ifExample3"
 (Input "Cond1" "1711548209594_47" iBool ∷
  Input "Cond2" "1711548209594_48" iBool ∷
  Input "Input1" "1711548209595_49" iInt16 ∷
  Input "Input2" "1711548209595_50" iInt16 ∷
  Input "Input3" "1711548209595_51" iInt16 ∷
  Input "Input4" "1711548253444_58" iInt16 ∷ [])
 (Output "Output" "1711548209596_18" iInt16 ∷ [])
 (If
  (Properties "If1" "1711548209596_5"
   ("1711548209598_53" ∷ "1711548209598_52" ∷ [])
   ((0 , "1711548209598_50") ∷ []) ("1711548209596_48" ∷ []) [])
  ∷
  Connection "Connect41" "1711548209596_48" "1711548209597_52"
  "1711548209596_5"
  ∷
  If
  (Properties "If2" "1711548209596_6"
   ("1711548209598_51" ∷ "1711548257535_58" ∷ [])
   ((0 , "1711548265539_59") ∷ []) ("1711548209598_49" ∷ []) [])
  ∷
  InputInstance
  (Properties "Cond1" "1711548209597_52" []
   ((0 , "1711548209596_48") ∷ []) [] [])
  "1711548209594_47"
  ∷
  InputInstance
  (Properties "Cond2" "1711548209597_53" []
   ((0 , "1711548209598_49") ∷ []) [] [])
  "1711548209594_48"
  ∷
  InputInstance
  (Properties "Input1" "1711548209597_54" []
   ((0 , "1711548209598_53") ∷ []) [] [])
  "1711548209595_49"
  ∷
  InputInstance
  (Properties "Input2" "1711548209597_55" []
   ((0 , "1711548209598_52") ∷ []) [] [])
  "1711548209595_50"
  ∷
  InputInstance
  (Properties "Input3" "1711548209598_56" []
   ((0 , "1711548209598_51") ∷ []) [] [])
  "1711548209595_51"
  ∷
  Connection "Connect42" "1711548209598_49" "1711548209597_53"
  "1711548209596_6"
  ∷
  Connection "Connect43" "1711548209598_50" "1711548209596_5"
  "1711548249118_9"
  ∷
  Connection "Connect44" "1711548209598_51" "1711548209598_56"
  "1711548209596_6"
  ∷
  Connection "Connect45" "1711548209598_52" "1711548209597_55"
  "1711548209596_5"
  ∷
  Connection "Connect46" "1711548209598_53" "1711548209597_54"
  "1711548209596_5"
  ∷
  Connection "Connect47" "1711548209598_54" "1711548249118_9"
  "1711548209598_19"
  ∷
  OutputInstance
  (Properties "Output" "1711548209598_19" ("1711548209598_54" ∷ [])
   [] [] [])
  "1711548209596_18"
  ∷
  Addition
  (Properties "Addition9" "1711548249118_9"
   ("1711548209598_50" ∷ "1711548265539_59" ∷ [])
   ((0 , "1711548209598_54") ∷ []) [] [])
  ∷
  InputInstance
  (Properties "Input4" "1711548253401_57" []
   ((0 , "1711548257535_58") ∷ []) [] [])
  "1711548253444_58"
  ∷
  Connection "Connect58" "1711548257535_58" "1711548253401_57"
  "1711548209596_6"
  ∷
  Connection "Connect59" "1711548265539_59" "1711548209596_6"
  "1711548249118_9"
  ∷ []))

previousExample : Model
previousExample = Operation "previous"
 (Input "Input" "1711905183406_46" iInt16 ∷ [])
 (Output "Output" "1711905218206_18" iInt16 ∷ [])
 (InputInstance
  (Properties "Input" "1711905183341_45" []
   ((0 , "1711905204184_49") ∷ []) [] [])
  "1711905183406_46"
  ∷
  Previous
  (Properties "Previous1" "1711905202015_1" ("1711905204184_49" ∷ [])
   ((0 , "1711905209522_50") ∷ []) [] ("" ∷ []))
  ("0" ∷ [])
  ∷
  Connection "Connect49" "1711905204184_49" "1711905183341_45"
  "1711905202015_1"
  ∷
  Connection "Connect50" "1711905209522_50" "1711905202015_1"
  "1711905218125_17"
  ∷
  OutputInstance
  (Properties "Output" "1711905218125_17" ("1711905209522_50" ∷ [])
   [] [] [])
  "1711905218206_18"
  ∷ [])
  
previousCycle : Model
previousCycle = Operation "previousCycle" []
 (Output "Output" "1713010148490_28" iInt16 ∷ [])
 (OutputInstance
  (Properties "Output" "1713010148462_27" ("1713010169932_75" ∷ [])
   [] [] [])
  "1713010148490_28"
  ∷
  Previous
  (Properties "Previous1" "1713010155494_6" ("1713010171125_76" ∷ [])
   ((0 , "1713010160524_73") ∷ []) [] ("" ∷ []))
  ("0" ∷ [])
  ∷
  Addition
  (Properties "Addition1" "1713010159611_11"
   ("1713010160524_73" ∷ "1713010165756_74" ∷ [])
   ((0 , "1713010169932_75") ∷ (0 , "1713010171125_76") ∷ []) [] [])
  ∷
  Connection "Connect73" "1713010160524_73" "1713010155494_6"
  "1713010159611_11"
  ∷
  Textual
  (Properties "Textual1" "1713010163528_1" []
   ((0 , "1713010165756_74") ∷ []) [] [])
  "1"
  ∷
  Connection "Connect74" "1713010165756_74" "1713010163528_1"
  "1713010159611_11"
  ∷
  Connection "Connect75" "1713010169932_75" "1713010159611_11"
  "1713010148462_27"
  ∷
  Connection "Connect76" "1713010171125_76" "1713010159611_11"
  "1713010155494_6"
  ∷ [])
  
previousCycle2 : Model
previousCycle2 = Operation "previousCycle2"
 (Input "Input1" "1713010102167_53" iInt16 ∷
  Input "Input2" "1713010102167_54" iInt16 ∷
  Input "Input5" "1713010102168_55" iInt16 ∷ [])
 (Output "Output1" "1713010102168_23" iInt16 ∷
  Output "Output3" "1713010102168_24" iInt16 ∷ [])
 (Addition
  (Properties "Addition1" "1713010102169_10"
   ("1713010102172_69" ∷
    "1713010102171_64" ∷ "1713010102170_62" ∷ "1713010102172_72" ∷ [])
   ((0 , "1713010102170_63") ∷
    (0 , "1713010102172_67") ∷ (0 , "1713010102172_71") ∷ [])
   [] [])
  ∷
  Previous
  (Properties "Previous1" "1713010102169_4" ("1713010102172_71" ∷ [])
   ((0 , "1713010102171_64") ∷ []) [] ("1713010102172_70" ∷ []))
  ("" ∷ [])
  ∷
  OutputInstance
  (Properties "Output1" "1713010102170_25" ("1713010102172_68" ∷ [])
   [] [] [])
  "1713010102168_23"
  ∷
  InputInstance
  (Properties "Input1" "1713010102170_56" []
   ((0 , "1713010102170_62") ∷ []) [] [])
  "1713010102167_53"
  ∷
  Connection "Connect4" "1713010102170_62" "1713010102170_56"
  "1713010102169_10"
  ∷
  OutputInstance
  (Properties "Output3" "1713010102170_26" ("1713010102170_63" ∷ [])
   [] [] [])
  "1713010102168_24"
  ∷
  Connection "Connect5" "1713010102170_63" "1713010102169_10"
  "1713010102170_26"
  ∷
  Connection "Connect11" "1713010102171_64" "1713010102169_4"
  "1713010102169_10"
  ∷
  Previous
  (Properties "Previous3" "1713010102171_5" ("1713010102172_67" ∷ [])
   ((0 , "1713010102171_65") ∷ []) [] ("" ∷ []))
  ("1" ∷ [])
  ∷
  Multiplication
  (Properties "Multiplication2" "1713010102171_3"
   ("1713010102171_65" ∷ "1713010102172_66" ∷ [])
   ((0 , "1713010102172_68") ∷ (0 , "1713010102172_69") ∷ []) [] [])
  ∷
  Connection "Connect62" "1713010102171_65" "1713010102171_5"
  "1713010102171_3"
  ∷
  InputInstance
  (Properties "Input2" "1713010102172_57" []
   ((0 , "1713010102172_66") ∷ []) [] [])
  "1713010102167_54"
  ∷
  Connection "Connect63" "1713010102172_66" "1713010102172_57"
  "1713010102171_3"
  ∷
  Connection "Connect66" "1713010102172_67" "1713010102169_10"
  "1713010102171_5"
  ∷
  Connection "Connect69" "1713010102172_68" "1713010102171_3"
  "1713010102170_25"
  ∷
  Connection "Connect70" "1713010102172_69" "1713010102171_3"
  "1713010102169_10"
  ∷
  InputInstance
  (Properties "Input5" "1713010102172_58" []
   ((0 , "1713010102172_70") ∷ (0 , "1713010102172_72") ∷ []) [] [])
  "1713010102168_55"
  ∷
  Connection "Connect76" "1713010102172_70" "1713010102172_58"
  "1713010102169_4"
  ∷
  Connection "Connect78" "1713010102172_71" "1713010102169_10"
  "1713010102169_4"
  ∷
  Connection "Connect79" "1713010102172_72" "1713010102172_58"
  "1713010102169_10"
  ∷ [])
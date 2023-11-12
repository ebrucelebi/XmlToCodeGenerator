{-# OPTIONS --safe #-}

module readIMODEFile where

open import parseXml
open import IMODEDataTypes
open import IMODESaveFile
open import Data.String
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Nat
open import Data.Char
open import Data.Bool
open import Relation.Nullary.Decidable

charToNat : Char -> Maybe ℕ
charToNat '0' = just 0
charToNat '1' = just 1
charToNat '2' = just 2
charToNat '3' = just 3
charToNat '4' = just 4
charToNat '5' = just 5
charToNat '6' = just 6
charToNat '7' = just 7
charToNat '8' = just 8
charToNat '9' = just 9
charToNat _ = nothing

reverseCharListToNat : List Char -> Maybe ℕ
reverseCharListToNat [] = just 0
reverseCharListToNat (x ∷ xs) with reverseCharListToNat xs | charToNat x
... | just r | just a = just (a + r * 10)
... | _ | _ = nothing

stringToNat : String -> Maybe ℕ
stringToNat s = reverseCharListToNat (reverse (toList s))

getDimensions : List XmlElement -> Maybe (List (ℕ))
getDimensions [] = just []
getDimensions ((Element "dimension" _ ((TextNode i) ∷ as)) ∷ xs) with getDimensions xs | stringToNat i
... | just ds | just d = just (d ∷ ds)
... | _ | _ = nothing
getDimensions _ = nothing

createArrayType : String -> List XmlElement -> Maybe Type
createArrayType n xs with getElement xs "arrayInfo"
createArrayType n xs | just (Element _ as es1) with getElement es1 "dimensions"
createArrayType n xs | just (Element _ as es1) | just (Element _ _ es2) with getDimensions es2 |  getAttributeValue as "definition"
createArrayType n xs | just (Element _ as es1) | just (Element _ _ es2) | just ds | just d with getType d
...                                                                                        | iNone = just (iArray n ds (iOther d))
...                                                                                        | t = just (iArray n ds t)
createArrayType n xs | just (Element _ as es1) | just (Element _ _ es2) | _ | _ = nothing
createArrayType n xs | just (Element _ as es1) | _ = nothing
createArrayType n xs | _ = nothing

createLabels : List XmlElement -> Maybe (List (String × Type))
createLabels [] = just []
createLabels ((Element "definitionElement" as _ ) ∷ xs) with createLabels xs | getAttributeValue as "name" | getAttributeValue as "definition"
createLabels ((Element "definitionElement" as _ ) ∷ xs) | just vs | just n | just d with getType d
...                                                                                 | iNone = just ((n , (iOther d)) ∷ vs)
...                                                                                 | t     = just ((n , t) ∷ vs)
createLabels ((Element "definitionElement" as _ ) ∷ xs) | _ | _ | _ = nothing
createLabels _ = nothing

createStructureType : String -> List XmlElement -> Maybe Type
createStructureType n xs with getElement xs "definitionElements"
createStructureType n xs | just (Element _ _ es) with createLabels es
...                                              | nothing = nothing
...                                              | just vs = just (iStructure n vs)
createStructureType n xs | _ = nothing

createEnumerationValues : List XmlElement -> Maybe (List String)
createEnumerationValues [] = just []
createEnumerationValues ((Element "definitionElement" as _) ∷ xs) with createEnumerationValues xs | getAttributeValue as "value"
... | just vs | just v = just (v ∷ vs)
... | _ | _ = nothing
createEnumerationValues _ = nothing

createEnumerationType : String -> List XmlElement -> Maybe Type
createEnumerationType n xs with getElement xs "definitionElements"
createEnumerationType n xs | just (Element _ _ es) with createEnumerationValues es
...                                                | nothing = nothing
...                                                | just vs = just (iEnum n vs)
createEnumerationType n xs | _ = nothing

createType : Maybe String -> Maybe String -> List XmlElement -> Maybe Type
createType (just n) (just "&lt;array&gt;") es = createArrayType n es
createType (just n) (just "&lt;structure&gt;") es = createStructureType n es
createType (just n) (just "&lt;enumeration&gt;") es = createEnumerationType n es
createType (just n) (just d) _ with getType d
... | iNone = just (iUserDefined n (iOther d))
... | t = just (iUserDefined n t)
createType _ _ _ = nothing

readTypes : List XmlElement -> Maybe (List Type)
readTypes [] = just []
readTypes ((Element "type" as es) ∷ xs) with readTypes xs | (createType (getAttributeValue as "name") (getAttributeValue as "definition") es)
... | just ts | just t = just (t ∷ ts)
... | _ | _ = nothing
readTypes _ = nothing

readTypesFile : Maybe XmlElement -> Maybe (List Type)
readTypesFile (just (Element "types" _ es)) = readTypes es
readTypesFile _ = nothing


createInterface : Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe Interface
createInterface (just n) (just d) (just io) (just v) (just c) with getType d
... | iNone = just record { name = n ; type = (iOther d) ; ioType = (getIOType io) ; value = v ; comment = c}
... | t     = just record { name = n ; type = t ;          ioType = (getIOType io) ; value = v ; comment = c}
createInterface _ _ _ _ _ = nothing

readInterfaces : List XmlElement -> Maybe (List Interface)
readInterfaces [] = just []
readInterfaces ((Element "interface" as es) ∷ xs) with readInterfaces xs | createInterface (getAttributeValue as "name") (getAttributeValue as "definition") (getAttributeValue as "IO" ) (getAttributeValue as "value") (getAttributeValue as "comment")
... | just is | just i = just (i ∷ is)
... | _ | _ = nothing
readInterfaces _ = nothing

readInterfacesFile : Maybe XmlElement -> Maybe (List Interface)
readInterfacesFile (just (Element "interfaces" _ es)) = readInterfaces es
readInterfacesFile _ = nothing


createConstant : Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe Constant
createConstant (just n) (just d) (just v) (just c) with getType d
... | iNone = just record { name = n ; type = (iOther d) ; value = v ; comment = c}
... | t     = just record { name = n ; type = t          ; value = v ; comment = c}
createConstant _ _ _ _ = nothing

readConstants : List XmlElement -> Maybe (List Constant)
readConstants [] = just []
readConstants ((Element "constant" as es) ∷ xs) with readConstants xs | createConstant(getAttributeValue as "name") (getAttributeValue as "definition") (getAttributeValue as "value") (getAttributeValue as "comment")
... | just cs | just c = just (c ∷ cs)
... | _ | _ = nothing
readConstants _ = nothing

readConstantsFile : Maybe XmlElement -> Maybe (List Constant)
readConstantsFile (just (Element "constants" _ es)) = readConstants es
readConstantsFile _ = nothing


createProject : Maybe String -> Maybe (List Type) ->  Maybe (List Interface) -> Maybe (List Constant) -> Maybe (List Model) -> Maybe Project
createProject (just n) (just ts) (just is) (just cs) (just fs) = just record { name = n ; subModels = fs ; types = ts ; interfaces = is ; constants = cs}
createProject _ _ _ _ _ = nothing


readInputConnectionIds : List XmlElement -> Maybe (List String)
readInputConnectionIds [] = just []
readInputConnectionIds ((Element "inputConnection" as _) ∷ xs) with readInputConnectionIds xs | getAttributeValue as "connectedTo"
... | just inConIds | just id = just (id ∷ inConIds)
... | _ | _ = nothing
readInputConnectionIds _ = nothing

readInputConnections : Maybe XmlElement -> Maybe (List String)
readInputConnections (just (Element "inputConnections" _ es)) = readInputConnectionIds es
readInputConnections _ = nothing


readOutputConnectionIds : List XmlElement -> Maybe (List (ℕ × String))
readOutputConnectionIds [] = just []
readOutputConnectionIds ((Element "outputConnection" as _) ∷ xs) with readOutputConnectionIds xs | getAttributeValue as "connectedTo" | getAttributeValue as "portOrder"
... | just outConIds | just id | just portOrderStr with stringToNat portOrderStr
... | just portOrder = just ((portOrder , id) ∷ outConIds)
... | _ = nothing
readOutputConnectionIds _ | _ | _ | _ = nothing
readOutputConnectionIds _ = nothing

readOutputConnections : Maybe XmlElement -> Maybe (List (ℕ × String))
readOutputConnections (just (Element "outputConnections" _ es)) = readOutputConnectionIds es
readOutputConnections _ = nothing


createBasicOpModelElement : String -> String -> String -> List XmlElement -> Maybe ModelElement
createBasicOpModelElement hash n id es with readInputConnections (getElement es "inputConnections") | readOutputConnections (getElement es "outputConnections")
... | just inCons | just outCons with Properties n id inCons outCons
... | p with hash
... | "955ca6d568f93954497d59e165f9fa9b" = just (Addition p)
... | "f8806a128e6f1a8d41cfa9b5f0f38f82" = just (Modulo p)
... | "c242c66d2b427ca579e166bcb7d29e13" = just (Multiplication p)
... | "f3717bffb869f6ff1fcce091f166f965" = just (NumericCast p)
... | "32d7b1f51ebe3b5ef0526278e223fcc9" = just (PolymorphicDivision p)
... | "8738acafef8eef7ddb3f91485d3ef88a" = just (Subtraction p)
... | "b69fd2eb52ec5bbe329447a438dd969a" = just (UnaryMinus p)
... | "bda26cfe60688578d081dd59071212cc" = just (LogicalAnd p)
... | "1bec680337697dc8b16c30e08df84a05" = just (LogicalNor p)
... | "5be489a447538f2bf9867665203e0561" = just (LogicalNot p)
... | "9c5febda3a36f236a93fdf532df6c5bf" = just (LogicalOr p)
... | "3c5ca129c2ad6f45890b03d9ea594927" = just (LogicalSharp p)
... | "5f857ecd847e60cf0b94eb8dfe61555e" = just (LogicalXor p)
... | "c9282e847e784046b17a01772be488c2" = just (BitwiseAnd p)
... | "bbc0c49eb5b7d5bee5435fc245c46c8d" = just (BitwiseNot p)
... | "c56b0df1c625a2184688ecc1076fbba5" = just (BitwiseOr p)
... | "7b3cbca16789893ffc523eb95d447f40" = just (BitwiseXor p)
... | "18c8a883eb26ba04ad7f346beae150ea" = just (LeftShift p)
... | "4ce5e6e4238b68f9ef8eb6cc79a89389" = just (RightShift p)
... | "e25f5536bb430d15c4ecf1c70674d1ae" = just (Different p)
... | "41f309026b7b989c3ae8dc03f41835d8" = just (Equal p)
... | "28ea640cc30fe446dd8f983de1e9a608" = just (GreaterThanEqual p)
... | "e2cdc9d4a7472ccc00f1700972004d71" = just (LessThanEqual p)
... | "c43404828b6fb52b32bbfe69adde0b63" = just (StrictlyGreaterThan p)
... | "10c8829be556be2c9869269b7d3782c2" = just (StrictlyLessThan p)
... | _ = nothing
createBasicOpModelElement hash n id es | _ | _ = nothing


createInput : String -> String -> List XmlElement -> Maybe ModelElement
createInput n id es with getElement es "sourceInstance"
createInput n id es | just e with getElement es "type"
createInput n id es | just e | just (Element _ as _) with getAttributeValue as "name"
...                                                  | nothing = nothing
...                                                  | just typeName = just (Input n id (getType typeName))
createInput n id es | just e | _ = nothing
createInput n id es | nothing with getElement es "copyOf"
createInput n id es | nothing | just (Element _ as _) with getAttributeValue as "value" | readOutputConnections (getElement es "outputConnections")
...                                                   | just sourceId | just outCons = just (InputInstance (Properties n id [] outCons) sourceId)
...                                                   | _ | _ = nothing
createInput n id es | nothing | _ = nothing


createOutput : String -> String -> List XmlElement -> Maybe ModelElement
createOutput n id es with getElement es "sourceInstance"
createOutput n id es | just e with getElement es "type"
createOutput n id es | just e | just (Element _ as _) with getAttributeValue as "name"
...                                                   | nothing = nothing
...                                                   | just typeName = just (Output n id (getType typeName))
createOutput n id es | just e | _ = nothing
createOutput n id es | nothing with getElement es "copyOf"
createOutput n id es | nothing | just (Element _ as _) with getAttributeValue as "value" | readInputConnections (getElement es "inputConnections")
...                                                    | just sourceId | just inCons = just (OutputInstance (Properties n id inCons []) sourceId)
...                                                    | _ | _ = nothing
createOutput n id es | nothing | _ = nothing


createConnection : String -> String -> List XmlElement -> Maybe ModelElement
createConnection n id es with getElement es "startOperation" | getElement es "endOperation"
... | just (Element "startOperation" as1 _) | just (Element "endOperation" as2 _) with getAttributeValue as1 "connectedTo" | getAttributeValue as2 "connectedTo"
... | just startOpId | just endOpId = just (Connection n id startOpId endOpId)
... | _ | _ = nothing
createConnection n id e | _ | _ = nothing


createModelElement : XmlElement -> Maybe ModelElement
createModelElement (Element "model" as es) with getAttributeValue as "name" | getAttributeValue as "id"
createModelElement (Element "model" as es) | just n | just id with getAttributeValue as "hash"
createModelElement (Element "model" as es) | just n | just id | just hash with hash
... | "47652e68b75f740d7c4228759d31a8f5" = createInput n id es
... | "1deb5a48a4655393a18760b265134ef3" = createOutput n id es
... | "c2459d3d1ef8a0b20f3e7125bae74582" = createConnection n id es
... | _ = createBasicOpModelElement hash n id es
createModelElement e | just n | just id | _  = nothing
createModelElement e | _      | _  = nothing
createModelElement _ = nothing


readModelElements : List XmlElement -> Maybe (List ModelElement)
readModelElements [] = just []
readModelElements ((Element n as es) ∷ xs) with readModelElements xs | getElement es "sourceInstance" | createModelElement (Element n as es)
... | just ms | nothing | just m = just (m ∷ ms)
... | just ms | just e  | _      = just ms
... | _       | _       | _      = nothing
readModelElements _ = nothing


findAndCreateModelWithId : List XmlElement -> String -> Maybe ModelElement
findAndCreateModelWithId [] _ = nothing
findAndCreateModelWithId ((Element n as es) ∷ xs) id with getAttributeValue as "id"
... | nothing = findAndCreateModelWithId xs id
... | just (otherId) with isYes (id Data.String.≟ otherId)
...         | false = findAndCreateModelWithId xs id
...         | true = createModelElement (Element n as es)
findAndCreateModelWithId (x ∷ xs) id = findAndCreateModelWithId xs id

readInputsForModel : List XmlElement -> List XmlElement -> Maybe (List ModelElement)
readInputsForModel [] _ = just []
readInputsForModel ((Element "startModel" as _) ∷ es) subModels with readInputsForModel es subModels | getAttributeValue as "hash"
readInputsForModel ((Element "startModel" as _) ∷ es) subModels | just startModels | just id with findAndCreateModelWithId subModels id
readInputsForModel ((Element "startModel" as _) ∷ es) subModels | just startModels | just id | just sm = just (sm ∷ startModels)
readInputsForModel ((Element "startModel" as _) ∷ es) subModels | _                | _       | _       = nothing
readInputsForModel ((Element "startModel" as _) ∷ es) subModels | _                | _       = nothing
readInputsForModel _ _ = nothing

readOutputsForModel : List XmlElement -> List XmlElement -> Maybe (List ModelElement)
readOutputsForModel [] _ = just []
readOutputsForModel ((Element "endModel" as _) ∷ es) subModels with readOutputsForModel es subModels | getAttributeValue as "hash"
readOutputsForModel ((Element "endModel" as _) ∷ es) subModels | just endModels | just id with findAndCreateModelWithId subModels id
readOutputsForModel ((Element "endModel" as _) ∷ es) subModels | just endModels | just id | just em = just (em ∷ endModels)
readOutputsForModel ((Element "endModel" as _) ∷ es) subModels | _              | _       | _       = nothing
readOutputsForModel ((Element "endModel" as _) ∷ es) subModels | _              | _       = nothing
readOutputsForModel _ _ = nothing

readModelFile : Maybe XmlElement -> Maybe Model
readModelFile (just (Element "model" as es)) with getAttributeValue as "name" | getElement es "submodels" | getElement es "startModels" | getElement es "endModels"
readModelFile (just (Element "model" as es)) | just n | just (Element _ _ sms) | just (Element _ _ es2) | just (Element _ _ es3) with readInputsForModel es2 sms | readOutputsForModel es3 sms | readModelElements sms
readModelFile (just (Element "model" as es)) | just n | just (Element _ _ sms) | just (Element _ _ es2) | just (Element _ _ es3) | just startModels | just endModels | just subModels = just (Operation n startModels endModels subModels)
readModelFile (just (Element "model" as es)) | _      | _                      | _                      | _                      | _                | _              | _              = nothing
readModelFile (just (Element "model" as es)) | _      | _                      | _                      | _                      = nothing
readModelFile _ = nothing

readModelFiles : List String -> Maybe (List Model)
readModelFiles [] = just []
readModelFiles (x ∷ xs) with readModelFiles xs | readModelFile (parseXml x)
... | just fs | just f = just (f ∷ fs)
... | _ | _ = nothing

readProjectFile : Maybe XmlElement -> Maybe Project
readProjectFile (just (Element "project" as es)) = createProject (getAttributeValue as "name") (readTypesFile (parseXml typesXmlString)) (readInterfacesFile (parseXml interfacesXmlString)) (readConstantsFile (parseXml constantsXmlString)) (readModelFiles modelXmlStrings)
readProjectFile _ = nothing


readIMODEFiles : Maybe Project
readIMODEFiles = readProjectFile (parseXml projectXmlString)

modelStr : String
modelStr = "<model tracedRequirements=\"\" visibility=\"1\" enable=\"1\" id=\"1696681110644_1\" name=\"Input1\" projectFileName=\"\" description=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-58\" xCoord=\"-400\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection connectedTo=\"1696681114575_1\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1696681110711_2\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>"

deneme : Maybe ModelElement
deneme with parseXml modelStr
deneme | nothing = just (Input "haha" "" iNone)
deneme | just (Element _ _ es) = createInput "a" "b" es
deneme | _ = just (TestModelElement 0)

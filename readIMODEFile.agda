{-# OPTIONS --guardedness #-}

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
reverseCharListToNat (x ∷ xs) with reverseCharListToNat xs
... | nothing = nothing
... | just r with charToNat x
... | nothing = nothing
... | just a = just (a + r * 10)

stringToNat : String -> Maybe ℕ
stringToNat s = reverseCharListToNat (reverse (toList s))

getDimensions : List XmlElement -> Maybe (List (ℕ))
getDimensions [] = just []
getDimensions ((Element "dimension" _ ((TextNode i) ∷ as)) ∷ xs) with getDimensions xs
... | nothing = nothing
... | just ds with stringToNat i
... | nothing = nothing
... | just d = just (d ∷ ds)
getDimensions _ = nothing

createArrayType : String -> List XmlElement -> Maybe Type
createArrayType n xs with getElement xs "arrayInfo"
... | nothing = nothing
... | just (TextNode _) = nothing
... | just (Element _ as es1) with getElement es1 "dimensions"
... | nothing = nothing
... | just (TextNode _) = nothing
... | just (Element _ _ es2) with getDimensions es2
... | nothing = nothing
... | just ds with getAttributeValue as "definition"
... | nothing = nothing
... | just d with getType d
... | iNone = just (iArray n ds (iOther d))
... | t = just (iArray n ds t)

createLabels : List XmlElement -> Maybe (List (String × Type))
createLabels [] = just []
createLabels ((Element "definitionElement" as _ ) ∷ xs) with createLabels xs
... | nothing = nothing
... | just vs with getAttributeValue as "name"
... | nothing = nothing
... | just n with getAttributeValue as "definition"
... | nothing = nothing
... | just d with getType d
... | iNone = just ((n , (iOther d)) ∷ vs)
... | t = just ((n , t) ∷ vs)
createLabels _ = nothing

createStructureType : String -> List XmlElement -> Maybe Type
createStructureType n xs with getElement xs "definitionElements"
... | nothing = nothing
... | just (TextNode _) = nothing
... | just (Element _ _ es) with createLabels es
... | nothing = nothing
... | just vs = just (iStructure n vs)

createEnumerationValues : List XmlElement -> Maybe (List String)
createEnumerationValues [] = just []
createEnumerationValues ((Element "definitionElement" as _) ∷ xs) with createEnumerationValues xs
... | nothing = nothing
... | just vs with getAttributeValue as "value"
... | nothing = nothing
... | just v = just (v ∷ vs)
createEnumerationValues _ = nothing

createEnumerationType : String -> List XmlElement -> Maybe Type
createEnumerationType n xs with getElement xs "definitionElements"
... | nothing = nothing
... | just (TextNode _) = nothing
... | just (Element _ _ es) with createEnumerationValues es
... | nothing = nothing
... | just vs = just (iEnum n vs)

createType : Maybe String -> Maybe String -> List XmlElement -> Maybe Type
createType nothing _ _ = nothing
createType _ nothing _ = nothing
createType (just n) (just "&lt;array&gt;") es = createArrayType n es
createType (just n) (just "&lt;structure&gt;") es = createStructureType n es
createType (just n) (just "&lt;enumeration&gt;") es = createEnumerationType n es
createType (just n) (just d) _ with getType d
... | iNone = just (iOther d)
... | t = just (iUserDefined n t)

readTypes : List XmlElement -> Maybe (List Type)
readTypes [] = just []
readTypes ((Element "type" as es) ∷ xs) with readTypes xs
... | nothing = nothing
... | just ts with (createType (getAttributeValue as "name") (getAttributeValue as "definition") es)
... | nothing = nothing
... | just t = just (t ∷ ts)
readTypes _ = nothing

readTypesFile : Maybe XmlElement -> Maybe (List Type)
readTypesFile (just (Element "types" _ es)) = readTypes es
readTypesFile _ = nothing


createInterface : Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe Interface
createInterface nothing _ _ _ _ = nothing
createInterface _ nothing _ _ _ = nothing
createInterface _ _ nothing _ _ = nothing
createInterface _ _ _ nothing _ = nothing
createInterface _ _ _ _ nothing = nothing
createInterface (just n) (just d) (just io) (just v) (just c) with getType d
... | iNone = just record { name = n ; type = (iOther d) ; ioType = (getIOType io) ; value = v ; comment = c}
... | t     = just record { name = n ; type = t ;          ioType = (getIOType io) ; value = v ; comment = c}

readInterfaces : List XmlElement -> Maybe (List Interface)
readInterfaces [] = just []
readInterfaces ((Element "interface" as es) ∷ xs) with readInterfaces xs
... | nothing = nothing
... | just is with createInterface (getAttributeValue as "name") (getAttributeValue as "definition") (getAttributeValue as "IO" ) (getAttributeValue as "value") (getAttributeValue as "comment")
... | nothing = nothing
... | just i = just (i ∷ is)
readInterfaces _ = nothing

readInterfacesFile : Maybe XmlElement -> Maybe (List Interface)
readInterfacesFile (just (Element "interfaces" _ es)) = readInterfaces es
readInterfacesFile _ = nothing


createConstant : Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe Constant
createConstant nothing _ _ _ = nothing
createConstant _ nothing _ _ = nothing
createConstant _ _ nothing _ = nothing
createConstant _ _ _ nothing = nothing
createConstant (just n) (just d) (just v) (just c) with getType d
... | iNone = just record { name = n ; type = (iOther d) ; value = v ; comment = c}
... | t     = just record { name = n ; type = t          ; value = v ; comment = c}

readConstants : List XmlElement -> Maybe (List Constant)
readConstants [] = just []
readConstants ((Element "constant" as es) ∷ xs) with readConstants xs
... | nothing = nothing
... | just cs with createConstant(getAttributeValue as "name") (getAttributeValue as "definition") (getAttributeValue as "value") (getAttributeValue as "comment")
... | nothing = nothing
... | just c = just (c ∷ cs)
readConstants _ = nothing

readConstantsFile : Maybe XmlElement -> Maybe (List Constant)
readConstantsFile (just (Element "constants" _ es)) = readConstants es
readConstantsFile _ = nothing


createProject : Maybe String -> Maybe (List Type) ->  Maybe (List Interface) -> Maybe (List Constant) -> Maybe (List Frame) -> Maybe Project
createProject nothing _ _ _ _ = nothing
createProject _ nothing _ _ _ = nothing
createProject _ _ nothing _ _ = nothing
createProject _ _ _ nothing _ = nothing
createProject _ _ _ _ nothing = nothing
createProject (just n) (just ts) (just is) (just cs) (just fs) = just record { name = n ; subModels = fs ; types = ts ; interfaces = is ; constants = cs}

createAddition : String -> String -> List XmlElement -> Maybe Model
createAddition n id es = just (Addition n id [])

createInput : String -> String -> List XmlElement -> Maybe Model
createInput n id es with getElement es "sourceInstance"
createInput n id es | just e with getElement es "type"
createInput n id es | just e | just (Element _ as _) with getAttributeValue as "name"
createInput n id es | just e | just (Element _ as _) | nothing = nothing
createInput n id es | just e | just (Element _ as _) | just typeName = just (Input n id (getType typeName))
createInput n id es | just e | _ = nothing
createInput n id es | nothing with getElement es "copyOf"
createInput n id es | nothing | just (Element _ as _) with getAttributeValue as "value"
createInput n id es | nothing | just (Element _ as _) | nothing = nothing
createInput n id es | nothing | just (Element _ as _) | just sourceId = just (InputInstance n id sourceId)
createInput n id es | nothing | _ = nothing

createOutput : String -> String -> List XmlElement -> Maybe Model
createOutput n id es with getElement es "sourceInstance"
createOutput n id es | just e with getElement es "type"
createOutput n id es | just e | just (Element _ as _) with getAttributeValue as "name"
createOutput n id es | just e | just (Element _ as _) | nothing = nothing
createOutput n id es | just e | just (Element _ as _) | just typeName = just (Output n id (getType typeName))
createOutput n id es | just e | _ = nothing
createOutput n id es | nothing with getElement es "copyOf"
createOutput n id es | nothing | just (Element _ as _) with getAttributeValue as "value"
createOutput n id es | nothing | just (Element _ as _) | nothing = nothing
createOutput n id es | nothing | just (Element _ as _) | just sourceId = just (OutputInstance n id sourceId)
createOutput n id es | nothing | _ = nothing

createConnection : String -> String -> List XmlElement -> Maybe Model
createConnection n id es = just (Connection n id "" "") 

createModel : XmlElement -> Maybe Model
createModel (Element "model" as es) with getAttributeValue as "name" | getAttributeValue as "id" | getAttributeValue as "hash"
... | just n | just id | just "955ca6d568f93954497d59e165f9fa9b" = createAddition n id es
... | just n | just id | just "47652e68b75f740d7c4228759d31a8f5" = createInput n id es
... | just n | just id | just "1deb5a48a4655393a18760b265134ef3" = createOutput n id es
... | just n | just id | just "c2459d3d1ef8a0b20f3e7125bae74582" = createConnection n id es
... | _      | _       | _                                       = nothing
createModel _ = nothing

readModels : List XmlElement -> Maybe (List Model)
readModels [] = just []
readModels ((Element n as es) ∷ xs) with readModels xs
... | nothing = nothing
... | just ms with getElement es "sourceInstance"
... | just e = just (ms)
... | _ with createModel (Element n as es)
... | nothing = nothing
... | just m = just (m ∷ ms)
readModels _ = nothing

findAndCreateModelWithId : List XmlElement -> String -> Maybe Model
findAndCreateModelWithId [] _ = nothing
findAndCreateModelWithId ((Element n as es) ∷ xs) id with getAttributeValue as "id"
... | nothing = findAndCreateModelWithId xs id
... | just (otherId) with isYes (id Data.String.≟ otherId)
... | false = findAndCreateModelWithId xs id
... | true = createModel (Element n as es)
findAndCreateModelWithId (x ∷ xs) id = findAndCreateModelWithId xs id

readStartModels : List XmlElement -> List XmlElement -> Maybe (List Model)
readStartModels [] _ = just []
readStartModels ((Element "startModel" as _) ∷ es) subModels with readStartModels es subModels
... | nothing = nothing
... | just startModels with getAttributeValue as "hash"
... | nothing = nothing
... | just id with findAndCreateModelWithId subModels id
... | nothing = nothing
... | just sm = just (sm ∷ startModels)
readStartModels _ _ = nothing

readEndModels : List XmlElement -> List XmlElement -> Maybe (List Model)
readEndModels [] _ = just []
readEndModels ((Element "endModel" as _) ∷ es) subModels with readEndModels es subModels
... | nothing = nothing
... | just endModels with getAttributeValue as "hash"
... | nothing = nothing
... | just id with findAndCreateModelWithId subModels id
... | nothing = nothing
... | just em = just (em ∷ endModels)
readEndModels _ _ = nothing

readFrameFile : Maybe XmlElement -> Maybe Frame
readFrameFile (just (Element "model" as es)) with getAttributeValue as "name"
... | nothing = nothing
... | just n with getElement es "submodels"
... | nothing = nothing
... | just (TextNode _) = nothing
... | just (Element _ _ sms) with getElement es "startModels"
... | nothing = nothing
... | just (TextNode _) = nothing
... | just (Element _ _ es2) with readStartModels es2 sms
... | nothing = nothing
... | just startModels with getElement es "endModels"
... | nothing = nothing
... | just (TextNode _) = nothing
... | just (Element _ _ es3) with readEndModels es3 sms
... | nothing = nothing
... | just endModels with readModels sms
... | nothing = nothing
... | just subModels = just (Operation n startModels endModels subModels)
readFrameFile _ = nothing

readFrameFiles : List String -> Maybe (List Frame)
readFrameFiles [] = just []
readFrameFiles (x ∷ xs) with readFrameFiles xs
... | nothing = nothing
... | just fs with readFrameFile (parseXml x)
... | nothing = nothing
... | just f = just (f ∷ fs)

readProjectFile : Maybe XmlElement -> Maybe Project
readProjectFile (just (Element "project" as es)) = createProject (getAttributeValue as "name") (readTypesFile (parseXml typesXmlString)) (readInterfacesFile (parseXml interfacesXmlString)) (readConstantsFile (parseXml constantsXmlString)) (readFrameFiles modelXmlStrings)
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

deneme : Maybe Model
deneme with parseXml modelStr
deneme | nothing = just (Input "haha" "" iNone)
deneme | just (Element _ _ es) = createInput "a" "b" es
deneme | _ = just (TestModel 0)

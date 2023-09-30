{-# OPTIONS --guardedness #-}

module readIMODEFile where

open import parseXml
open import IMODEDataTypes
open import IMODESaveFile
open import Data.String
open import Data.List
open import Data.Maybe
open import Data.Product

createProject : String -> Project
createProject n = record { name = n ; subModels = [] ; types = [] ; interfaces = [] ; constants = []}

readProjectFile : XmlElement -> Maybe Project
readProjectFile (Element "project" as es) with getAttributeValue as "name"
... | just s = just (createProject s)
... | nothing = nothing
readProjectFile _ = nothing


createArrayType : String -> List XmlElement -> Maybe Type
createArrayType _ _ = nothing

createLabels : List XmlElement -> Maybe (List (String × Type))
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
createEnumerationValues ((Element "definitionElement" as _) ∷ xs) with createEnumerationValues xs
... | nothing = nothing
... | just vs = nothing -- Look at xml save of enumerations
createEnumerationValues _ = nothing

createEnumerationType : String -> List XmlElement -> Maybe Type
createEnumerationType n xs with createEnumerationValues xs
... | nothing = nothing
... | just vs = just (iEnum n vs)

createType : Maybe String -> Maybe String -> List XmlElement -> Maybe Type
createType nothing _ _ = nothing
createType _ nothing _ = nothing
createType (just n) (just "array") es = createArrayType n es
createType (just n) (just "structure") es = createStructureType n es
createType (just n) (just "enumeration") es = createEnumerationType n es
createType (just n) (just d) _ with getType d
... | iNone = just (iOther d)
... | t = just (iUserDefined n t)

readTypes : List XmlElement -> Maybe (List Type)
readTypes ((Element "type" as es) ∷ xs) with readTypes xs
... | nothing = nothing
... | just ts with (createType (getAttributeValue as "name") (getAttributeValue as "definition") es)
... | nothing = nothing
... | just t = just (t ∷ ts)
readTypes _ = just []

readTypesFile : XmlElement -> Maybe (List Type)
readTypesFile (Element "types" _ es) = readTypes es
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
readInterfaces ((Element "interface" as es) ∷ xs) with readInterfaces xs
... | nothing = nothing
... | just is with createInterface (getAttributeValue as "name") (getAttributeValue as "definition") (getAttributeValue as "IO" ) (getAttributeValue as "value") (getAttributeValue as "comment")
... | nothing = nothing
... | just i = just (i ∷ is)
readInterfaces _ = just []

readInterfacesFile : XmlElement -> Maybe (List Interface)
readInterfacesFile (Element "types" _ es) = readInterfaces es
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
readConstants ((Element "type" as es) ∷ xs) with readConstants xs
... | nothing = nothing
... | just cs with createConstant(getAttributeValue as "name") (getAttributeValue as "definition") (getAttributeValue as "value") (getAttributeValue as "comment")
... | nothing = nothing
... | just c = just (c ∷ cs)
readConstants _ = just []

readConstantsFile : XmlElement -> Maybe (List Constant)
readConstantsFile (Element "types" _ es) = readConstants es
readConstantsFile _ = nothing

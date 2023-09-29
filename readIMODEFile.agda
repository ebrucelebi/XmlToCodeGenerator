{-# OPTIONS --guardedness #-}

module readIMODEFile where

open import parseXml
open import IMODEDataTypes
open import IMODESaveFile
open import Data.String
open import Data.List
open import Data.Maybe

createProject : String -> Project
createProject n = record { name = n ; subModels = [] ; types = [] ; interfaces = [] ; constants = []}

readProjectFile : XmlElement -> Maybe Project
readProjectFile (Element "project" as es) with getAttributeValue as "name"
... | just s = just (createProject s)
... | nothing = nothing
readProjectFile _ = nothing


createArrayType : String -> List XmlElement -> Maybe Type
createArrayType _ _ = nothing

createStructureType : String -> List XmlElement -> Maybe Type
createStructureType _ _ = nothing

createEnumerationType : String -> List XmlElement -> Maybe Type
createEnumerationType _ _ = nothing

createType : Maybe String -> Maybe String -> List XmlElement -> Maybe Type
createType nothing _ _ = nothing
createType _ nothing _ = nothing
createType (just n) (just "array") es = createArrayType n es
createType (just n) (just "structure") es = createStructureType n es
createType (just n) (just "enumeration") es = createEnumerationType n es
createType (just n) (just d) _ with getType d
... | iNone = just (iUserDefined d)
... | t = just (iOther n t)


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
createInterface (just n) (just d) (just io) (just v) (just c) = just record { name = n ; type = iBool; ioType = (getIOType io); value = v; comment = c}


readInterfaces : List XmlElement -> Maybe (List Type)
readInterfaces ((Element "interface" as es) ∷ xs) = just []
readInterfaces _ = just []

readInterfacesFile : XmlElement -> Maybe (List Type)
readInterfacesFile (Element "types" _ es) = readInterfaces es
readInterfacesFile _ = nothing



readConstants : List XmlElement -> Maybe (List Type)
readConstants ((Element "type" as es) ∷ xs) = just []
readConstants _ = just []

readConstantsFile : XmlElement -> Maybe (List Type)
readConstantsFile (Element "types" _ es) = readInterfaces es
readConstantsFile _ = nothing

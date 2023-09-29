{-# OPTIONS --guardedness #-}

module readIMODEFile where

open import parseXml
open import IMODEDataTypes
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

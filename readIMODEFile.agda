{-# OPTIONS --guardedness #-}

module readIMODEFile where

open import parseXml
open import IMODEDataTypes
open import Data.String
open import Data.List

createProject : String -> Project
createProject n = record { name = n ; subModels = [] ; types = [] ; interfaces = [] ; constants = []}

readIMODEFile : XmlElement -> Project
readIMODEFile _ = createProject ""

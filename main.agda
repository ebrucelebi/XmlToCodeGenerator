{-# OPTIONS --guardedness #-}

module main where

open import Data.Maybe
open import Data.List
open import IO
open import parseXml
open import IMODESaveFile

main : Maybe XmlElement
main = parseXml imodeString

{-# OPTIONS --guardedness #-}

module main where

open import Data.Char
open import Data.List
open import Data.Maybe
open import Data.String
open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality


-- Read the XML file into a string.
xmlString : String
xmlString = "<note>
        <to>Tove</to>
	<from>Jani</from>
	<heading>Reminder</heading>
	<body>weekend!</body>
</note>"

data XmlAttribute : Set where
  Attribute : (name : String) -> String -> XmlAttribute
  
data XmlElement : Set where
  Element : (name : String) -> List XmlAttribute -> List XmlElement -> XmlElement
  TextNode : String -> XmlElement

record ElemPair : Set where
  field
    name : String
    content : List String

parseTokens : List Char -> List Char -> List String
parseTokens [] _ = []
parseTokens ('<' ∷ '/' ∷ xs) (' ' ∷ []) = "</" ∷ parseTokens xs [] -- End element tag prefix
parseTokens ('<' ∷ '/' ∷ xs) b  = (fromList b) ∷ "</" ∷ parseTokens xs [] -- End element tag prefix
parseTokens ('/' ∷ '>' ∷ xs) b  = "/>" ∷ parseTokens xs b -- Empty element tag postfix
parseTokens ('<' ∷ xs) b = "<" ∷ parseTokens xs [] -- Tag prefix
parseTokens ('>' ∷ xs) b = (fromList b) ∷ ">" ∷ parseTokens xs [] -- Tag postfix
parseTokens ('=' ∷ xs) b = [] -- Attribute
parseTokens (' ' ∷ xs) [] = parseTokens xs (' ' ∷ []) -- Skip
parseTokens ('\n' ∷ xs) [] = parseTokens xs (' ' ∷ []) -- Skip
parseTokens ('\t' ∷ xs) [] = parseTokens xs (' ' ∷ []) -- Skip
parseTokens ('\r' ∷ xs) [] = parseTokens xs (' ' ∷ []) -- Skip
parseTokens (' ' ∷ xs) (' ' ∷ []) = parseTokens xs (' ' ∷ []) -- Skip
parseTokens ('\n' ∷ xs) (' ' ∷ []) = parseTokens xs (' ' ∷ []) -- Skip
parseTokens ('\t' ∷ xs) (' ' ∷ []) = parseTokens xs (' ' ∷ []) -- Skip
parseTokens ('\r' ∷ xs) (' ' ∷ []) = parseTokens xs (' ' ∷ []) -- Skip
parseTokens (x ∷ xs) b = parseTokens xs (b Data.List.++ Data.List.[_] x)

getBetweenElem : List String -> List String -> ℕ -> Maybe ElemPair
getBetweenElem ("</" ∷ nm ∷ ">" ∷ []) bf 0 = just record { name = nm ; content = bf}
getBetweenElem ("</" ∷ xs) bf (suc n) = getBetweenElem xs (bf Data.List.++ Data.List.[_] "</") n
getBetweenElem ("<" ∷ xs) bf n = getBetweenElem xs (bf Data.List.++ Data.List.[_] "<") (suc n)
getBetweenElem (x ∷ xs) bf n = getBetweenElem xs (bf Data.List.++ Data.List.[_] x) n
getBetweenElem _ _ _ = nothing

splitElementStrings : List String -> List String -> List (List String)
splitElementStrings ("</" ∷ nm ∷ ">" ∷ xs) bf = (bf Data.List.++ ("</" ∷ nm ∷ ">" ∷ xs)) ∷ splitElementStrings xs []
splitElementStrings (x ∷ xs) bf = splitElementStrings xs (bf Data.List.++ Data.List.[_] x)
splitElementStrings [] _ = []

mutual
  parseElementHelper : Maybe ElemPair -> Maybe XmlElement
  parseElementHelper (just (record {name = n ; content = bf})) with (parseElements (splitElementStrings bf []))
  ... | just elems = just (Element n [] elems)
  ... | nothing  = nothing
  parseElementHelper _ = nothing

  parseElement : List String -> Maybe XmlElement
  parseElement ("<" ∷ xs) with (parseElementHelper (getBetweenElem xs [] 0))
  ... | just elem = just elem
  ... | nothing = nothing
  parseElement (x ∷ xs) = nothing
  parseElement [] = nothing

  parseElementsHelper : Maybe XmlElement -> List (List String) -> Maybe (List XmlElement)
  parseElementsHelper (just e) (xs) with (parseElements xs)
  ... | just elems = just (e ∷ elems)
  ... | nothing = nothing
  parseElementsHelper nothing _  = nothing

  parseElements : List (List String) -> Maybe (List XmlElement)
  parseElements [] = nothing
  parseElements (x ∷ xs) =  parseElementsHelper (parseElement x) xs

parseClosingTag : List String -> Maybe (List String)
parseClosingTag _ = nothing

parseXml : String -> Maybe XmlElement
parseXml input with parseTokens (toList input) []
... | "<" ∷ xs = parseElement ("<" ∷ xs)
... | tokens = nothing -- If it does not start with start element tag, it is faulty.
  
parseAttributes : List String -> Maybe (List XmlAttribute)
parseAttributes _  = nothing

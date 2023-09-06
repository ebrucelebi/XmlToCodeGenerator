{-# OPTIONS --guardedness #-}

module main where

open import Data.Char
open import Data.List
open import Data.Maybe
open import Data.String
open import Data.Nat
open import Data.Bool
open import Relation.Nullary.Decidable

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

-- Xml content, started element buffer, resulting element
parseElement : List String -> List XmlElement -> Maybe XmlElement 
parseElement ("<" ∷ name ∷ ">" ∷ xs) elemBuff = parseElement xs ((Element name [] []) ∷ elemBuff)
parseElement ("</" ∷ name1 ∷ ">" ∷ xs) ((Element name2 as es) ∷ []) with isYes (name1 Data.String.≟ name2)
... | true = just (Element name1 as es)
... | false = nothing
parseElement (x ∷ xs) elemBuff = parseElement xs elemBuff
parseElement [] _ = nothing

parseXml : String -> Maybe XmlElement
parseXml input = parseElement (parseTokens (toList input) []) []
  
parseAttributes : List String -> Maybe (List XmlAttribute)
parseAttributes _  = nothing

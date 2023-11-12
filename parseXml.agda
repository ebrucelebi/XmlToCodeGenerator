{-# OPTIONS --safe #-}

module parseXml where

open import Data.Char
open import Data.List
open import Data.Maybe
open import Data.String
open import Data.Nat
open import Data.Bool
open import Relation.Nullary.Decidable

data XmlAttribute : Set where
  Attribute : (name : String) -> String -> XmlAttribute
  
data XmlElement : Set where
  Element : (name : String) -> List XmlAttribute -> List XmlElement -> XmlElement
  TextNode : String -> XmlElement

appendToList : ∀{ℓ}{A : Set ℓ} → List A → A → List A
appendToList l e = (l Data.List.++ Data.List.[_] e)

appendToElement : XmlElement → XmlElement → XmlElement
appendToElement (Element n as es) e2 = Element n as (appendToList es e2)
appendToElement e _ = e

appendAttribute : XmlElement -> XmlAttribute -> XmlElement
appendAttribute (Element n as es) a = Element n (appendToList as a) es
appendAttribute e _ = e

-- Xml content, buffer for string, element started, string started if true (accept spaces), parsed tokens
parseTokens : List Char -> List Char -> Bool -> Bool -> List String
parseTokens [] _ _ _ = []
parseTokens ('<' ∷ '/' ∷ xs) [] _ _   = "</" ∷ parseTokens xs [] false false -- End element tag prefix
parseTokens ('<' ∷ '/' ∷ xs) b _ _    = (fromList b) ∷ "</" ∷ parseTokens xs [] false false -- End element tag prefix
parseTokens ('/' ∷ '>' ∷ xs) [] _ _   = "/>" ∷ parseTokens xs [] false false -- Empty element tag postfix
parseTokens ('/' ∷ '>' ∷ xs) b _ _    = (fromList b) ∷ "/>" ∷ parseTokens xs [] false false -- Empty element tag postfix
parseTokens ('<' ∷ xs) _ _ _          = "<" ∷ parseTokens xs [] true false -- Tag prefix
parseTokens ('>' ∷ xs) [] true _      = ">" ∷ parseTokens xs [] false true -- Tag postfix
parseTokens ('>' ∷ xs) b true _       = (fromList b) ∷ ">" ∷ parseTokens xs [] false true -- Tag postfix
parseTokens ('>' ∷ xs) b false _      = (fromList b) ∷ ">" ∷ parseTokens xs [] false false -- Tag postfix
parseTokens ('=' ∷ xs) b true _       = (fromList b) ∷ "=" ∷ parseTokens xs [] true false -- Attribute
parseTokens (' ' ∷ xs) [] true false  = parseTokens xs [] true false -- Between attributes
parseTokens (' ' ∷ xs) b true false   = (fromList b) ∷ parseTokens xs [] true false -- Element name done might start attributes
parseTokens (' ' ∷ xs) b e false      = parseTokens xs b e false -- Skip
parseTokens ('\n' ∷ xs) b e false     = parseTokens xs b e false -- Skip
parseTokens ('\t' ∷ xs) b e false     = parseTokens xs b e false -- Skip
parseTokens ('\r' ∷ xs) b e false     = parseTokens xs b e false -- Skip
parseTokens ('\"' ∷ xs) b true false  = parseTokens xs [] true true -- Attribute value started
parseTokens ('\"' ∷ xs) b true true   = (fromList b) ∷ parseTokens xs [] true false -- Attribute value ended
parseTokens (x ∷ xs) b e s            = parseTokens xs (appendToList b x) e s

-- Xml content, started element buffer, resulting element
parseElement : List String -> List XmlElement -> Maybe XmlElement 
parseElement ("<" ∷ name ∷ ">" ∷ xs) elemBuff = parseElement xs ((Element name [] []) ∷ elemBuff)
parseElement ("</" ∷ name1 ∷ ">" ∷ xs) ((Element name2 as es) ∷ []) with isYes (name1 Data.String.≟ name2)
... | true = just (Element name1 as es)
... | false = nothing
parseElement ("</" ∷ name1 ∷ ">" ∷ xs) ((Element name2 as es) ∷ p ∷ elemBuff) with isYes (name1 Data.String.≟ name2)
... | true = parseElement xs ((appendToElement p (Element name2 as es)) ∷ elemBuff)
... | false = nothing
parseElement (">" ∷ xs) elemBuff = parseElement xs elemBuff -- Just start tag ended
parseElement ("/>" ∷ xs) (p ∷ []) = just p
parseElement ("/>" ∷ xs) (e ∷ p ∷ elemBuff) = parseElement xs ((appendToElement p e) ∷ elemBuff)
parseElement ("<" ∷ name ∷ "/>" ∷ xs) [] = just (Element name [] [])
parseElement ("<" ∷ name ∷ "/>" ∷ xs) (p ∷ elemBuff) = parseElement xs ((appendToElement p (Element name [] [])) ∷ elemBuff)
parseElement ("<" ∷ name ∷ xs) elemBuff = parseElement xs ((Element name [] []) ∷ elemBuff) -- Start tag with attributes
parseElement (att ∷ "=" ∷ val ∷ xs) (e ∷ elemBuff) = parseElement xs ((appendAttribute e (Attribute att val)) ∷ elemBuff)
parseElement (x ∷ xs) (p ∷ elemBuff) = parseElement xs ((appendToElement p (TextNode x)) ∷ elemBuff)
parseElement _ _ = nothing

parseXml : String -> Maybe XmlElement
parseXml input = parseElement (parseTokens (toList input) [] false false) []

getAttributeValue : List XmlAttribute -> String -> Maybe String
getAttributeValue ((Attribute n1 v) ∷ xs) n2 with isYes (n1 Data.String.≟ n2)
... | true = just v
... | false = getAttributeValue xs n2
getAttributeValue [] _ = nothing

getElement : List XmlElement -> String -> Maybe XmlElement
getElement ((Element n1 as es) ∷ xs) n2 with isYes (n1 Data.String.≟ n2)
... | true = just (Element n1 as es)
... | false = getElement xs n2
getElement _ _ = nothing

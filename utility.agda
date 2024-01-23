{-# OPTIONS --safe #-}

module utility where

open import Data.List
open import Data.Char hiding (_==_)
open import Data.String
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Relation.Nullary.Decidable

appendToList : ∀{ℓ}{A : Set ℓ} → List A → A → List A
appendToList l e = (l Data.List.++ Data.List.[_] e)

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

contains : List String -> String -> Bool
contains [] _ = false
contains (x ∷ xs) y with x == y
... | true = true
... | false = contains xs y

concatenate : ∀{ℓ}{A : Set ℓ} → List (List A) → List A
concatenate [] = []
concatenate (x ∷ xs) = x Data.List.++ concatenate xs

getElementAtIndex : ∀{ℓ}{A : Set ℓ} -> List A -> ℕ -> Maybe A
getElementAtIndex [] _ = nothing
getElementAtIndex (x ∷ xs) zero = just x
getElementAtIndex (x ∷ xs) (suc n) = getElementAtIndex xs n

concatenateTwoList : ∀{ℓ}{A : Set ℓ} → List A -> List A → List A
concatenateTwoList xs1 xs2 = xs1 Data.List.++ xs2

_==ℕ_ : ℕ -> ℕ -> Bool
_==ℕ_ n m = isYes (n Data.Nat.≟ m)

_!=ℕ_ : ℕ -> ℕ -> Bool
_!=ℕ_ n m = isNo (n Data.Nat.≟ m)

_>=ℕ_ : ℕ -> ℕ -> Bool
_>=ℕ_ n m = isYes (n Data.Nat.≥? m)

max : ℕ -> ℕ -> ℕ
max zero n = n
max n zero = n
max (suc n) (suc m) = max n m

join : List String -> String -> String
join [] _ = ""
join (x ∷ []) _ = x
join (x ∷ xs) y = x Data.String.++ y Data.String.++ (join xs y)

lastString : String -> Maybe Char
lastString s = last (toList s)
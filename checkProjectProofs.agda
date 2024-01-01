{-# OPTIONS --safe #-}
module checkProjectProofs where

open import utility
open import checkProject
open import IMODEDataTypes

open import Data.List
open import Data.Bool
open import Data.String
open import Relation.Binary.PropositionalEquality

-- Requirement 1: Input model elements shall not have any input points.
req1-1 : ∀ {n id outCons sID} -> checkInputConnectionCounts (InputInstance (Properties n id [] outCons) sID) ≡ true
req1-1 = refl

req1-2 : ∀ {n id outCons sID x xs} -> checkInputConnectionCounts (InputInstance (Properties n id (x ∷ xs) outCons) sID) ≡ false
req1-2 = refl

-- Requirement 2: Output model elements shall have only one input point.
req2-1 : ∀ {n id outCons sID x} -> checkInputConnectionCounts (OutputInstance (Properties n id (x ∷ []) outCons) sID) ≡ true
req2-1 = refl

req2-2 : ∀ {n id outCons sID} -> checkInputConnectionCounts (OutputInstance (Properties n id [] outCons) sID) ≡ false
req2-2 = refl

req2-3 : ∀ {n id outCons sID x y xs} -> checkInputConnectionCounts (OutputInstance (Properties n id (x ∷ y ∷ xs) outCons) sID) ≡ false
req2-3 = refl

-- Requirement 3: Addition model elements shall have 2 or more input points.
req3-1 : ∀ {n id outCons x y xs} -> checkInputConnectionCounts (Addition (Properties n id (x ∷ y ∷ xs) outCons)) ≡ true
req3-1 = refl

req3-2 : ∀ {n id outCons} -> checkInputConnectionCounts (Addition (Properties n id [] outCons)) ≡ false
req3-2 = refl

req3-3 : ∀ {n id outCons x} -> checkInputConnectionCounts (Addition (Properties n id (x ∷ []) outCons)) ≡ false
req3-3 = refl

-- Requirement 4: Modulo model elements shall have only 2 input points.
req4-1 : ∀ {n id outCons x y} -> checkInputConnectionCounts (Modulo (Properties n id (x ∷ y ∷ []) outCons)) ≡ true
req4-1 = refl

req4-2 : ∀ {n id outCons} -> checkInputConnectionCounts (Modulo (Properties n id [] outCons)) ≡ false
req4-2 = refl

req4-3 : ∀ {n id outCons x} -> checkInputConnectionCounts (Modulo (Properties n id (x ∷ []) outCons)) ≡ false
req4-3 = refl

req4-4 : ∀ {n id outCons x y z xs} -> checkInputConnectionCounts (Modulo (Properties n id (x ∷ y ∷ z ∷ xs) outCons)) ≡ false
req4-4 = refl

-- Requirement 5: Multiplication model elements shall have 2 or more input points.
req5-1 : ∀ {n id outCons x y xs} -> checkInputConnectionCounts (Multiplication (Properties n id (x ∷ y ∷ xs) outCons)) ≡ true
req5-1 = refl

req5-2 : ∀ {n id outCons} -> checkInputConnectionCounts (Multiplication (Properties n id [] outCons)) ≡ false
req5-2 = refl

req5-3 : ∀ {n id outCons x} -> checkInputConnectionCounts (Multiplication (Properties n id (x ∷ []) outCons)) ≡ false
req5-3 = refl

-- Requirement 6: NumericCast model elements shall have only 1 input point.
req6-1 : ∀ {n id outCons x} -> checkInputConnectionCounts (NumericCast (Properties n id (x ∷ []) outCons)) ≡ true
req6-1 = refl

req6-2 : ∀ {n id outCons} -> checkInputConnectionCounts (NumericCast (Properties n id [] outCons)) ≡ false
req6-2 = refl

req6-3 : ∀ {n id outCons x y xs} -> checkInputConnectionCounts (NumericCast (Properties n id (x ∷ y ∷ xs) outCons)) ≡ false
req6-3 = refl

-- Requirement 7: PolymorphicDivision model elements shall have only 2 input points.
req7-1 : ∀ {n id outCons x y} -> checkInputConnectionCounts (PolymorphicDivision (Properties n id (x ∷ y ∷ []) outCons)) ≡ true
req7-1 = refl

req7-2 : ∀ {n id outCons} -> checkInputConnectionCounts (PolymorphicDivision (Properties n id [] outCons)) ≡ false
req7-2 = refl

req7-3 : ∀ {n id outCons x} -> checkInputConnectionCounts (PolymorphicDivision (Properties n id (x ∷ []) outCons)) ≡ false
req7-3 = refl

req7-4 : ∀ {n id outCons x y z xs} -> checkInputConnectionCounts (PolymorphicDivision (Properties n id (x ∷ y ∷ z ∷ xs) outCons)) ≡ false
req7-4 = refl

-- Requirement 8: Subtraction model elements shall have only 2 input points.
req8-1 : ∀ {n id outCons x y} -> checkInputConnectionCounts (Subtraction (Properties n id (x ∷ y ∷ []) outCons)) ≡ true
req8-1 = refl

req8-2 : ∀ {n id outCons} -> checkInputConnectionCounts (Subtraction (Properties n id [] outCons)) ≡ false
req8-2 = refl

req8-3 : ∀ {n id outCons x} -> checkInputConnectionCounts (Subtraction (Properties n id (x ∷ []) outCons)) ≡ false
req8-3 = refl

req8-4 : ∀ {n id outCons x y z xs} -> checkInputConnectionCounts (Subtraction (Properties n id (x ∷ y ∷ z ∷ xs) outCons)) ≡ false
req8-4 = refl

-- Requirement 9: UnaryMinus model elements shall have only 1 input point.
req9-1 : ∀ {n id outCons x} -> checkInputConnectionCounts (UnaryMinus (Properties n id (x ∷ []) outCons)) ≡ true
req9-1 = refl

req9-2 : ∀ {n id outCons} -> checkInputConnectionCounts (UnaryMinus (Properties n id [] outCons)) ≡ false
req9-2 = refl

req9-3 : ∀ {n id outCons x y xs} -> checkInputConnectionCounts (UnaryMinus (Properties n id (x ∷ y ∷ xs) outCons)) ≡ false
req9-3 = refl
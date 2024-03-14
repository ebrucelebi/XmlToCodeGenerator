{-# OPTIONS --safe #-}

module HoareLogic where

open import utility

open import Data.List
open import Data.Maybe
open import Data.Bool hiding (_<_; _∧_)
open import Data.Nat hiding (_+_; _*_; _^_; _>_; _<_)
open import Data.String hiding (_==_; _<_)
open import Agda.Builtin.Equality

data Var : Set where
    var_ : String -> Var

data Annotation : Set where
    _+_  : Annotation -> Annotation -> Annotation
    _-_  : Annotation -> Annotation -> Annotation
    _*_  : Annotation -> Annotation -> Annotation
    _/_  : Annotation -> Annotation -> Annotation
    -_   : Annotation -> Annotation
    _&&_ : Annotation -> Annotation -> Annotation
    !_   : Annotation -> Annotation
    _||_ : Annotation -> Annotation -> Annotation
    _^_  : Annotation -> Annotation -> Annotation
    _&_  : Annotation -> Annotation -> Annotation
    ~_   : Annotation -> Annotation
    _|b_ : Annotation -> Annotation -> Annotation
    _<<_ : Annotation -> Annotation -> Annotation
    _>>_ : Annotation -> Annotation -> Annotation
    _!=_ : Annotation -> Annotation -> Annotation
    _==_ : Annotation -> Annotation -> Annotation
    _>=_ : Annotation -> Annotation -> Annotation
    _<=_ : Annotation -> Annotation -> Annotation
    _>_  : Annotation -> Annotation -> Annotation
    _<_  : Annotation -> Annotation -> Annotation
    const_ : ℕ -> Annotation
    var_ : String -> Annotation

infixr 5 _∧_
infixr 6 _:=:_
data Condition : Set where
    test : String -> Condition
    true : Condition
    false : Condition
    Defined_ : Var -> Condition
    _:=:_ : Var -> Annotation -> Condition -- Equality predicate
    _∧_ : Condition -> Condition -> Condition
    -- _∨_ : Condition -> Condition -> Condition

data HoareTriplet {a} (A : Set a): Set a where
    ⟪_⟫_⟪_⟫ : Condition -> A -> Condition -> HoareTriplet A

_≟A_ : Annotation -> Annotation -> Bool
_≟A_ (const n1) (const n2) = n1 ==ℕ n2
_≟A_ (var v1) (var v2) = v1 Data.String.== v2
_≟A_ (_+_  a1 a2) (_+_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_-_  a1 a2) (_-_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_*_  a1 a2) (_*_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_/_  a1 a2) (_/_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (-_   a1)    (-_   a3)    = (a1 ≟A a3)
_≟A_ (_&&_ a1 a2) (_&&_ a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (!_   a1)    (!_   a3)    = (a1 ≟A a3)
_≟A_ (_||_ a1 a2) (_||_ a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_^_  a1 a2) (_^_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_&_  a1 a2) (_&_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (~_   a1)    (~_   a3)    = (a1 ≟A a3)
_≟A_ (_|b_ a1 a2) (_|b_ a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_<<_ a1 a2) (_<<_ a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_>>_ a1 a2) (_>>_ a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_!=_ a1 a2) (_!=_ a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_==_ a1 a2) (_==_ a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_>=_ a1 a2) (_>=_ a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_<=_ a1 a2) (_<=_ a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_>_  a1 a2) (_>_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_<_  a1 a2) (_<_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ _ _ = false

infix 4 _≟C_
_≟C_ : Condition -> Condition -> Bool
true                ≟C true                 = true
false               ≟C false                = true
Defined (var n1)    ≟C Defined (var n2)     = n1 Data.String.== n2
(c1 ∧ c2)           ≟C c3                   = (c1 ≟C c3) Data.Bool.∨ (c2 ≟C c3)
c1                  ≟C (c2 ∧ c3)            = (c1 ≟C c2) Data.Bool.∨ (c1 ≟C c3)
(var n1) :=: a1     ≟C (var n2) :=: a2      = (n1 Data.String.== n2) Data.Bool.∧ (a1 ≟A a2)
_                   ≟C _                    = false

containsVar : List Var -> Var -> Bool
containsVar [] _ = false
containsVar ((var x) ∷ xs) (var y) with x Data.String.== y
... | true = true
... | false = containsVar xs (var y)

replaceVar : Condition -> Var -> Maybe Annotation
replaceVar (Defined (var x)) (var v) with x Data.String.== v
... | true = just (var x)
... | false = nothing
replaceVar ((var x) :=: e) (var v) with x Data.String.== v
... | true = just e
... | false = nothing
replaceVar (a1 ∧ a2) v with replaceVar a1 v
... | just e1 = just e1
... | nothing = replaceVar a2 v
replaceVar _ _ = nothing

replaceVars : Condition -> Annotation -> Maybe Annotation
replaceVars a (var v) = replaceVar a (var v)
replaceVars a (e1 + e2) with replaceVars a e1 | replaceVars a e2
... | just e1' | just e2' = just (e1' + e2')
... | _ | _ = nothing
replaceVars a (e1 * e2) with replaceVars a e1 | replaceVars a e2
... | just e1' | just e2' = just (e1' * e2')
... | _ | _ = nothing
replaceVars _ e = nothing

weaken : Condition -> List Var -> Condition
weaken (v :=: a) vs with containsVar vs v
... | true = (v :=: a)
... | false = true
weaken (c1 ∧ c2) vs with weaken c1 vs | weaken c2 vs
... | false | wc2 = false
... | wc1 | false = false
... | true | wc2 = wc2
... | wc1 | true = wc1
... | wc1 | wc2 = wc1 ∧ wc2
weaken c _ = c

a : Condition
a = ((var "x") :=: (const 2)) ∧ ((var "y") :=: (const 1))

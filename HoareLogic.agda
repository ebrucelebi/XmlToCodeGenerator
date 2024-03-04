{-# OPTIONS --safe #-}

module HoareLogic where

open import Data.List
open import Data.Bool hiding (_<_; _∧_)
open import Data.Nat hiding (_+_; _*_; _^_; _>_; _<_)
open import Data.String hiding (_==_; _<_)

data Var : Set where
    var_ : String -> Var

data Annotation : Set where
    _+_ : Annotation -> Annotation -> Annotation
    _-_ : Annotation -> Annotation -> Annotation
    _*_ : Annotation -> Annotation -> Annotation
    _/_ : Annotation -> Annotation -> Annotation
    -_ : Annotation -> Annotation
    _&&_ : Annotation -> Annotation -> Annotation
    !_ : Annotation -> Annotation
    _||_ : Annotation -> Annotation -> Annotation
    _^_ : Annotation -> Annotation -> Annotation
    _&_ : Annotation -> Annotation -> Annotation
    ~_ : Annotation -> Annotation
    _|b_ : Annotation -> Annotation -> Annotation
    _<<_ : Annotation -> Annotation -> Annotation
    _>>_ : Annotation -> Annotation -> Annotation
    _!=_ : Annotation -> Annotation -> Annotation
    _==_ : Annotation -> Annotation -> Annotation
    _>=_ : Annotation -> Annotation -> Annotation
    _<=_ : Annotation -> Annotation -> Annotation
    _>_ : Annotation -> Annotation -> Annotation
    _<_ : Annotation -> Annotation -> Annotation
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
    <_>_<_> : Condition -> A -> Condition -> HoareTriplet A

containsVar : List Var -> Var -> Bool
containsVar [] _ = false
containsVar ((var x) ∷ xs) (var y) with x Data.String.== y
... | true = true
... | false = containsVar xs (var y)

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

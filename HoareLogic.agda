{-# OPTIONS --safe #-}

module HoareLogic where

open import Data.Nat hiding (_+_; _*_; _^_; _>_; _<_)
open import Data.String hiding (_==_; _<_)

data Var : Set where
    var_ : String -> Var

data Exp : Set where
    _+_ : Exp -> Exp -> Exp
    _-_ : Exp -> Exp -> Exp
    _*_ : Exp -> Exp -> Exp
    _/_ : Exp -> Exp -> Exp
    -_ : Exp -> Exp
    _&&_ : Exp -> Exp -> Exp
    !_ : Exp -> Exp
    _||_ : Exp -> Exp -> Exp
    _^_ : Exp -> Exp -> Exp
    _&_ : Exp -> Exp -> Exp
    ~_ : Exp -> Exp
    _|b_ : Exp -> Exp -> Exp
    _<<_ : Exp -> Exp -> Exp
    _>>_ : Exp -> Exp -> Exp
    _!=_ : Exp -> Exp -> Exp
    _==_ : Exp -> Exp -> Exp
    _>=_ : Exp -> Exp -> Exp
    _<=_ : Exp -> Exp -> Exp
    _>_ : Exp -> Exp -> Exp
    _<_ : Exp -> Exp -> Exp
    const_ : ℕ -> Exp
    var_ : String -> Exp

infixr 5 _∧_
infixr 6 _:=_
data Annotation : Set where
    test : String -> Annotation
    true : Annotation
    false : Annotation
    Defined_ : Var -> Annotation
    _:=_ : Var -> Exp -> Annotation
    _∧_ : Annotation -> Annotation -> Annotation
    -- _∨_ : Annotation -> Annotation -> Annotation

a : Annotation
a = ((var "x") := (const 2)) ∧ ((var "y") := (const 1))

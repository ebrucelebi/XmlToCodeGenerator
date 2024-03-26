{-# OPTIONS --safe #-}

module HoareLogic where

open import utility

open import Data.List
open import Data.Maybe
open import Data.Bool hiding (_<_; _∧_; _∨_)
open import Data.Nat hiding (_+_; _*_; _^_; _>_; _<_)
open import Data.String hiding (_==_; _<_; _++_)
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
    true : Annotation
    false : Annotation

infixr 5 _∧_
infixr 6 _:=:_
data Condition : Set where
    test : String -> Condition
    true : Condition
    false : Condition
    Defined_ : Var -> Condition
    _:=:_ : Annotation -> Annotation -> Condition -- Equality predicate
    _∧_ : Condition -> Condition -> Condition
    _∨_ : Condition -> Condition -> Condition

data HoareTriplet {a} (A : Set a): Set a where
    ⟪_⟫_⟪_⟫ : Condition -> A -> Condition -> HoareTriplet A

_≟A_ : Annotation -> Annotation -> Bool
_≟A_ false false = true
_≟A_ true true = true
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
(c1 ∧ c2)           ≟C (c3 ∧ c4)            = (c1 ≟C c3) Data.Bool.∧ (c2 ≟C c4)
(c1 ∨ c2)           ≟C (c3 ∨ c4)            = (c1 ≟C c3) Data.Bool.∧ (c2 ≟C c4)
a1 :=: a2           ≟C a3 :=: a4            = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_                   ≟C _                    = false

findConditionForVar : Condition -> Var -> Maybe Condition
findConditionForVar (Defined (var v1)) (var v2) with v1 Data.String.== v2
... | true = just (Defined (var v1))
... | false = nothing
findConditionForVar ((var v1) :=: a) (var v2) with v1 Data.String.== v2
... | true = just ((var v1) :=: a)
... | false = nothing
findConditionForVar (c1 ∧ c2) v with findConditionForVar c1 v
... | just c = just c
... | nothing with findConditionForVar c2 v
... | just c = just c
... | nothing = nothing
findConditionForVar (c1 ∨ c2) v with findConditionForVar c1 v
... | just c = just (c1 ∨ c2)
... | nothing with findConditionForVar c2 v
... | just c = just (c1 ∨ c2)
... | nothing = nothing
findConditionForVar _ _ = nothing

weaken : Condition -> List Var -> Condition
weaken c [] = true
weaken c (v ∷ []) with findConditionForVar c v
... | nothing = true
... | just c1 = c1
weaken c (v ∷ vs) with findConditionForVar c v
... | nothing = weaken c vs
... | just c1 = c1 ∧ weaken c vs

replaceVarInAnnotation : Annotation -> Var -> Annotation -> Annotation
replaceVarInAnnotation (var v1) (var v2) a with v1 Data.String.== v2
... | true = a
... | false = (var v1)
replaceVarInAnnotation (_+_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 + replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_-_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 - replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_*_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 * replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_/_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 / replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (-_   a1)    v a3 = - replaceVarInAnnotation a1 v a3 
replaceVarInAnnotation (_&&_ a1 a2) v a3 = replaceVarInAnnotation a1 v a3 && replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (!_   a1)    v a3 = ! replaceVarInAnnotation a1 v a3 
replaceVarInAnnotation (_||_ a1 a2) v a3 = replaceVarInAnnotation a1 v a3 || replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_^_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 ^ replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_&_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 & replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (~_   a1)    v a3 = ~ replaceVarInAnnotation a1 v a3 
replaceVarInAnnotation (_|b_ a1 a2) v a3 = replaceVarInAnnotation a1 v a3 |b replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_<<_ a1 a2) v a3 = replaceVarInAnnotation a1 v a3 << replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_>>_ a1 a2) v a3 = replaceVarInAnnotation a1 v a3 >> replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_!=_ a1 a2) v a3 = replaceVarInAnnotation a1 v a3 != replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_==_ a1 a2) v a3 = replaceVarInAnnotation a1 v a3 == replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_>=_ a1 a2) v a3 = replaceVarInAnnotation a1 v a3 >= replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_<=_ a1 a2) v a3 = replaceVarInAnnotation a1 v a3 <= replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_>_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 > replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_<_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 < replaceVarInAnnotation a2 v a3
replaceVarInAnnotation a _ _ = a

replaceVarsInNewAnnotation : Condition -> Annotation -> Annotation
replaceVarsInNewAnnotation (Defined (var v1)) a = a
replaceVarsInNewAnnotation ((var v1) :=: a1) a2 = replaceVarInAnnotation a2 (var v1) a1
-- replaceVarsInNewAnnotation ((a1 :=: true ∧ c1) ∨ (a2 :=: false ∧ c2)) a3 with replaceVarsInNewAnnotation c1 a3 | replaceVarsInNewAnnotation c2 a3
-- ... | c13 | c23 with c13 ≟A c3 | c23 ≟A c3
-- ... | true | true = a3
-- ... | _ | _ = (a1 :=: true ∧ c13) ∨ (a2 :=: false ∧ c23)
replaceVarsInNewAnnotation (c1 ∧ c2) a3 = replaceVarsInNewAnnotation c1 (replaceVarsInNewAnnotation c2 a3)
-- replaceVarsInNewAnnotation preC ((a1 :=: true ∧ c1) ∨ (a2 :=: false ∧ c2)) = (a1 :=: true ∧ replaceVarsInNewCondition preC c1) ∨ (a2 :=: false ∧ replaceVarsInNewCondition preC c2)
replaceVarsInNewAnnotation _ a = a

replaceVarsInNewCondition : Condition -> Condition -> Condition
replaceVarsInNewCondition true c = c
replaceVarsInNewCondition (Defined (var v1)) c = c
replaceVarsInNewCondition ((var v1) :=: a1) ((var v2) :=: a2) = (var v2) :=: replaceVarInAnnotation a2 (var v1) a1
replaceVarsInNewCondition ((a1 :=: true ∧ c1) ∨ (a2 :=: false ∧ c2)) c3 with replaceVarsInNewCondition c1 c3 | replaceVarsInNewCondition c2 c3
... | c13 | c23 with c13 ≟C c3 | c23 ≟C c3
... | true | true = c3
... | _ | _ = (a1 :=: true ∧ c13) ∨ (a2 :=: false ∧ c23)
replaceVarsInNewCondition (c1 ∧ c2) c3 = replaceVarsInNewCondition c1 (replaceVarsInNewCondition c2 c3)
replaceVarsInNewCondition preC ((a1 :=: true ∧ c1) ∨ (a2 :=: false ∧ c2)) =
    (replaceVarsInNewAnnotation preC a1 :=: true ∧ replaceVarsInNewCondition preC c1) ∨
    (replaceVarsInNewAnnotation preC a2 :=: false ∧ replaceVarsInNewCondition preC c2)
replaceVarsInNewCondition _ _ = false

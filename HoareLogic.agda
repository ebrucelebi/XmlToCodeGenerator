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
    _%_  : Annotation -> Annotation -> Annotation
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
    const_ : String -> Annotation
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
_≟A_ (const s1) (const s2) = s1 Data.String.== s2
_≟A_ (var v1) (var v2) = v1 Data.String.== v2
_≟A_ (_+_  a1 a2) (_+_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_-_  a1 a2) (_-_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_*_  a1 a2) (_*_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_/_  a1 a2) (_/_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
_≟A_ (_%_  a1 a2) (_%_  a3 a4) = (a1 ≟A a3) Data.Bool.∧ (a2 ≟A a4)
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

findVarInCondition : Condition -> Maybe Var
findVarInCondition (Defined (var v)) = just (var v)
findVarInCondition ((var v) :=: a) = just (var v)
findVarInCondition ((a1 :=: true ∧ c1) ∨ (a2 :=: false ∧ c2)) = findVarInCondition c1
findVarInCondition _ = nothing

replaceVarInAnnotation : Annotation -> Var -> Annotation -> Annotation
replaceVarInAnnotation (var v1) (var v2) a with v1 Data.String.== v2
... | true = a
... | false = (var v1)
replaceVarInAnnotation (_+_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 + replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_-_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 - replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_*_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 * replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_/_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 / replaceVarInAnnotation a2 v a3
replaceVarInAnnotation (_%_  a1 a2) v a3 = replaceVarInAnnotation a1 v a3 % replaceVarInAnnotation a2 v a3
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
replaceVarsInNewCondition true                                          c                   = c
replaceVarsInNewCondition _                                             true                = true
replaceVarsInNewCondition _                                             false               = false
replaceVarsInNewCondition _                                             (Defined v)         = (Defined v)
replaceVarsInNewCondition (Defined (var v1))                            c                   = c
replaceVarsInNewCondition ((var v1) :=: a1)                             ((var v2) :=: a2)   = (var v2) :=: replaceVarInAnnotation a2 (var v1) a1
replaceVarsInNewCondition ((a1 :=: true ∧ c1) ∨ (a2 :=: false ∧ c2))    c3                  with replaceVarsInNewCondition c1 c3 | replaceVarsInNewCondition c2 c3
... | c13 | c23 with c13 ≟C c3 | c23 ≟C c3
... | true | true = c3
... | _ | _ = (a1 :=: true ∧ c13) ∨ (a2 :=: false ∧ c23)
replaceVarsInNewCondition preC                                          ((a1 :=: true ∧ c1) ∨ (a2 :=: false ∧ c2)) =
    (replaceVarsInNewAnnotation preC a1 :=: true ∧ replaceVarsInNewCondition preC c1) ∨
    (replaceVarsInNewAnnotation preC a2 :=: false ∧ replaceVarsInNewCondition preC c2)
replaceVarsInNewCondition preC                                          (c1 ∧ c2) = replaceVarsInNewCondition preC c1 ∧ replaceVarsInNewCondition preC c2
replaceVarsInNewCondition (c1 ∧ c2)                                     c3 = replaceVarsInNewCondition c1 (replaceVarsInNewCondition c2 c3)
replaceVarsInNewCondition _ _ = false

varAppearsInDefinitionA : Annotation -> Var -> Bool
varAppearsInDefinitionA (var v1) (var v2) = v1 Data.String.== v2
varAppearsInDefinitionA (_+_  a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_-_  a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_*_  a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_/_  a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_%_  a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (-_   a1)    v = varAppearsInDefinitionA a1 v
varAppearsInDefinitionA (_&&_ a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (!_   a1)    v = varAppearsInDefinitionA a1 v
varAppearsInDefinitionA (_||_ a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_^_  a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_&_  a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (~_   a1)    v = varAppearsInDefinitionA a1 v
varAppearsInDefinitionA (_|b_ a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_<<_ a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_>>_ a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_!=_ a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_==_ a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_>=_ a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_<=_ a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_>_  a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA (_<_  a1 a2) v = (varAppearsInDefinitionA a1 v) Data.Bool.∨ (varAppearsInDefinitionA a2 v)
varAppearsInDefinitionA _ _ = false

varAppearsInDefinitionC : Condition -> Maybe Var -> Bool
varAppearsInDefinitionC ((var v1) :=: a1) (just v2) = varAppearsInDefinitionA a1 v2
varAppearsInDefinitionC ((a1 :=: true ∧ c1) ∨ (a2 :=: false ∧ c2)) (just v2) = varAppearsInDefinitionC c1 (just v2) Data.Bool.∨
                                                                               varAppearsInDefinitionC c2 (just v2) Data.Bool.∨
                                                                               varAppearsInDefinitionA a1 v2 Data.Bool.∨
                                                                               varAppearsInDefinitionA a2 v2
varAppearsInDefinitionC _ _ = false

checkAndReplaceVarsInNewCondition : Condition -> Condition -> Condition
checkAndReplaceVarsInNewCondition c1 (c2 ∧ c3) = checkAndReplaceVarsInNewCondition c1 c2 ∧ checkAndReplaceVarsInNewCondition c1 c3
checkAndReplaceVarsInNewCondition c1 c2 with replaceVarsInNewCondition c1 c2
... | replacedC with varAppearsInDefinitionC replacedC (findVarInCondition c2)
... | false = replacedC
... | true = c2

getConditionsWithVars : Condition -> List Var -> Condition
getConditionsWithVars c [] = true
getConditionsWithVars c (v ∷ []) with findConditionForVar c v
... | nothing = true
... | just c1 = c1
getConditionsWithVars c (v ∷ vs) with findConditionForVar c v
... | nothing = getConditionsWithVars c vs
... | just c1 = c1 ∧ getConditionsWithVars c vs

checkConditionVarAppearsInCondition : Condition -> Condition -> Bool
checkConditionVarAppearsInCondition c1 (c2 ∧ c3) = checkConditionVarAppearsInCondition c1 c2 Data.Bool.∨ checkConditionVarAppearsInCondition c1 c3
checkConditionVarAppearsInCondition c1 c2 = varAppearsInDefinitionC c2 (findVarInCondition c1)

containsVar : List Var -> Var -> Bool
containsVar [] v = false
containsVar ((var v1) ∷ vs) (var v2) with v1 Data.String.== v2
... | true = true
... | false = containsVar vs (var v2) 

removeConditionsWithUnusedVars : Condition -> Condition -> List Var -> Condition
removeConditionsWithUnusedVars (c1 ∧ c2) c3 mustV with removeConditionsWithUnusedVars c1 c3 mustV | removeConditionsWithUnusedVars c2 c3 mustV
... | true | true = true
... | true | c1 = c1
... | c1 | true = c1
... | c1 | c2 = c1 ∧ c2
removeConditionsWithUnusedVars c1 c2 mustV with findVarInCondition c1
... | just v with containsVar mustV v
... | true = c1
... | false with checkConditionVarAppearsInCondition c1 c2
... | true = c1
... | false = true
removeConditionsWithUnusedVars c1 c2 mustV | nothing = c1

weaken : Condition -> List Var -> List Var -> Condition
weaken c vs mustV = let cs = getConditionsWithVars c vs in removeConditionsWithUnusedVars cs cs mustV

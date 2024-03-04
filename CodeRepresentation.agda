{-# OPTIONS --safe #-}

module CodeRepresentation where

open import HoareLogic

open import Data.Bool hiding (_∧_)
open import Data.String
open import Data.Maybe
open import Data.List hiding (_++_)
open import Data.Vec hiding (_++_)
open import Relation.Binary.PropositionalEquality

data Oper : Set where
    Addition : Oper
    Subtraction : Oper
    Multiplication : Oper
    Division : Oper
    Minus : Oper
    LogicalAnd : Oper
    LogicalNot : Oper
    LogicalOr : Oper
    LogicalXor : Oper
    BitwiseAnd : Oper
    BitwiseNot : Oper
    BitwiseOr : Oper
    BitwiseXor : Oper
    LeftShift : Oper
    RightShift : Oper
    Different : Oper
    Equal : Oper
    GreaterThanEqual : Oper
    LessThanEqual : Oper
    StrictlyGreaterThan : Oper
    StrictlyLessThan : Oper

data Code : Set where
    Variable : String -> Code
    Expression : Code -> Oper -> Code -> Code
    LeftExpression : Code -> Oper -> Code
    RightExpression : Oper -> Code -> Code

data StatementType : Set where
    EmptyStatement : StatementType
    Statement : String -> Code -> StatementType

joinToExpression : List String -> Oper -> Code
joinToExpression [] _ = Variable "" -- Should not come here
joinToExpression (x ∷ []) _ = Variable x
joinToExpression (x ∷ xs) o = Expression (Variable x) o (joinToExpression xs o)

operationToString : Oper -> String
operationToString Addition = "+"
operationToString Subtraction = "-"
operationToString Multiplication = "*"
operationToString Division = "/"
operationToString Minus = "-"
operationToString LogicalAnd = "&&"
operationToString LogicalNot = "!"
operationToString LogicalOr = "||"
operationToString LogicalXor = "^"
operationToString BitwiseAnd = "&"
operationToString BitwiseNot = "~"
operationToString BitwiseOr = "|"
operationToString BitwiseXor = "^"
operationToString LeftShift = "<<"
operationToString RightShift = ">>"
operationToString Different = "!="
operationToString Equal = "=="
operationToString GreaterThanEqual = ">="
operationToString LessThanEqual = "<="
operationToString StrictlyGreaterThan = ">"
operationToString StrictlyLessThan = "<"

codeToString : Code -> String
codeToString (Variable s) = s
codeToString (Expression l o r) = codeToString l ++ " " ++ operationToString o ++ " " ++ codeToString r
codeToString (LeftExpression l o) = codeToString l ++ " " ++ operationToString o
codeToString (RightExpression o r) = operationToString o ++ " " ++ codeToString r

statementToString : StatementType -> String
statementToString EmptyStatement = ""
statementToString (Statement v c) = (v ++ " = " ++ codeToString c ++ ";")

statementListToString : List StatementType -> List String
statementListToString [] = []
statementListToString (x ∷ xs) = statementToString x ∷ statementListToString xs

codeToAnnotation : Code -> Annotation
codeToAnnotation (Variable x) = var x
codeToAnnotation (Expression c1 Addition c2) = (codeToAnnotation c1) + (codeToAnnotation c2)
codeToAnnotation (Expression c1 Subtraction c2) = (codeToAnnotation c1) - (codeToAnnotation c2)
codeToAnnotation (Expression c1 Multiplication c2) = (codeToAnnotation c1) * (codeToAnnotation c2)
codeToAnnotation (Expression c1 Division c2) = (codeToAnnotation c1) / (codeToAnnotation c2)
codeToAnnotation _ = const 0

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

statementToCondition : Condition -> StatementType -> Condition
statementToCondition false _ = false
statementToCondition a EmptyStatement = a
statementToCondition a (Statement x c) with replaceVars a (codeToAnnotation c)
... | just e = (var x) :=: e
... | nothing = false

statementListToCondition : Condition -> List StatementType -> Condition
statementListToCondition a [] = a
statementListToCondition a (x ∷ xs) = statementListToCondition (a ∧ (statementToCondition a x)) xs

statementListToHoareTriplets : Condition -> List StatementType -> List (HoareTriplet String)
statementListToHoareTriplets a [] = (< a > (statementToString EmptyStatement) < false >) ∷ [] -- Should not come here
statementListToHoareTriplets a (x ∷ []) = let pC = (a ∧ (statementToCondition a x)) in 
                                    < a > (statementToString x) < pC > ∷ []
statementListToHoareTriplets a (x ∷ xs) = let pC = (a ∧ (statementToCondition a x)) in 
                                    < a > (statementToString x) < pC > ∷ (statementListToHoareTriplets pC xs)

testAnn : Condition
testAnn = Defined (var "In1") ∧
          Defined (var "In2") ∧
          (var "Input1") :=: (var "In1") + (var "In2")

exp : Code
exp = Expression (Variable "Input1") Addition (Variable "In2")

denemeState : StatementType
denemeState = Statement "Addition1" exp

deneme : List (HoareTriplet String)
deneme = statementListToHoareTriplets testAnn (denemeState ∷ [])

deneme2 : Maybe Annotation
deneme2 = replaceVars testAnn (codeToAnnotation exp)

deneme3 : Maybe Annotation
deneme3 = replaceVars testAnn ((var "Input1") + (var "In2"))  
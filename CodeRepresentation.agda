{-# OPTIONS --safe #-}

module CodeRepresentation where

open import HoareLogic

open import Data.Bool hiding (_∧_)
open import Data.String
open import Data.Maybe
open import Data.List hiding (_++_)
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

statementListToString : List StatementType -> List String
statementListToString [] = []
statementListToString ((Statement v c) ∷ xs) = (v ++ " = " ++ codeToString c ++ ";") ∷ statementListToString xs

codeToExp : Code -> Exp
codeToExp (Variable x) = var x
codeToExp (Expression c1 Addition c2) = (codeToExp c1) + (codeToExp c2)
codeToExp (Expression c1 Subtraction c2) = (codeToExp c1) - (codeToExp c2)
codeToExp (Expression c1 Multiplication c2) = (codeToExp c1) * (codeToExp c2)
codeToExp (Expression c1 Division c2) = (codeToExp c1) / (codeToExp c2)
codeToExp _ = const 0

replaceVar : Annotation -> Var -> Maybe Exp
replaceVar (Defined (var x)) (var v) with x Data.String.== v
... | true = just (var x)
... | false = nothing
replaceVar ((var x) := e) (var v) with x Data.String.== v
... | true = just e
... | false = nothing
replaceVar (a1 ∧ a2) v with replaceVar a1 v
... | just e1 = just e1
... | nothing = replaceVar a2 v
replaceVar _ _ = nothing

replaceVars : Annotation -> Exp -> Maybe Exp
replaceVars a (var v) = replaceVar a (var v)
replaceVars a (e1 + e2) with replaceVars a e1 | replaceVars a e2
... | just e1' | just e2' = just (e1' + e2')
... | _ | _ = nothing
replaceVars a (e1 * e2) with replaceVars a e1 | replaceVars a e2
... | just e1' | just e2' = just (e1' * e2')
... | _ | _ = nothing
replaceVars _ e = nothing

statementToAnnotation : Annotation -> StatementType -> Annotation
statementToAnnotation false _ = false
statementToAnnotation a (Statement x c) with replaceVars a (codeToExp c)
... | just e = (var x) := e
... | nothing = test "2"

statementListToAnnotation : Annotation -> List StatementType -> Annotation
statementListToAnnotation false _ = test "1"
statementListToAnnotation a [] = a
statementListToAnnotation a (x ∷ xs) = statementListToAnnotation (a ∧ (statementToAnnotation a x)) xs

testAnn : Annotation
testAnn = Defined (var "In1") ∧ Defined (var "In2") ∧ (var "Input1") := (var "In1") + (var "In2")

exp : Code
exp = Expression (Variable "Input1") Addition (Variable "In2")

denemeState : StatementType
denemeState = Statement "Addition1" exp

deneme : Annotation
deneme = statementListToAnnotation testAnn (denemeState ∷ [])

deneme2 : Maybe Exp
deneme2 = replaceVars testAnn (codeToExp exp)

deneme3 : Maybe Exp
deneme3 = replaceVars testAnn ((var "Input1") + (var "In2"))  
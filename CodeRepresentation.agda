{-# OPTIONS --safe #-}

module CodeRepresentation where

open import HoareLogic

open import Data.String
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

statementToAnnotation : Annotation -> StatementType -> Annotation
statementToAnnotation false _ = false
statementToAnnotation a (Statement x c) = (var x) := (codeToExp c)

deneme : StatementType
deneme = Statement "Addition1" (Expression (Variable "Input1") Addition (Variable "Input2"))

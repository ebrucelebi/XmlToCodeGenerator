{-# OPTIONS --safe #-}

module CodeRepresentation where

open import HoareLogic

open import Data.Bool hiding (_∧_; _∨_)
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
    IfStatement : Code -> List StatementType -> List StatementType -> StatementType

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

indent : List String -> List String
indent [] = []
indent (x ∷ xs) = ("    " Data.String.++ x) ∷ indent xs

encapsulateBraces : List String -> List String
encapsulateBraces l = ("{" ∷ indent l) Data.List.++ ("}" ∷ [])

mutual
    statementToString : StatementType -> List String
    statementToString EmptyStatement = "" ∷ []
    statementToString (IfStatement c t f) = (("if (" ++ (codeToString c) ++ ")") ∷
                                            (encapsulateBraces (statementListToString t))) Data.List.++
                                            ("else" ∷
                                            (encapsulateBraces (statementListToString f)))
    statementToString (Statement v c) = (v ++ " = " ++ codeToString c ++ ";") ∷ []

    statementListToString : List StatementType -> List String
    statementListToString [] = []
    statementListToString (x ∷ xs) = statementToString x Data.List.++ statementListToString xs

codeToAnnotation : Code -> Annotation
codeToAnnotation (Variable x) = var x
codeToAnnotation (Expression c1 Addition c2) = (codeToAnnotation c1) + (codeToAnnotation c2)
codeToAnnotation (Expression c1 Subtraction c2) = (codeToAnnotation c1) - (codeToAnnotation c2)
codeToAnnotation (Expression c1 Multiplication c2) = (codeToAnnotation c1) * (codeToAnnotation c2)
codeToAnnotation (Expression c1 Division c2) = (codeToAnnotation c1) / (codeToAnnotation c2)
codeToAnnotation (Expression c1 StrictlyGreaterThan c2) = (codeToAnnotation c1) > (codeToAnnotation c2)
codeToAnnotation _ = const 0

mutual
    statementToCondition : Condition -> StatementType -> Condition
    statementToCondition false _ = false
    statementToCondition a EmptyStatement = true
    statementToCondition a (Statement x c) = (var x) :=: codeToAnnotation c
    statementToCondition a (IfStatement c t f) = let cc = codeToAnnotation c in
     (statementListToCondition a (cc :=: true) t) ∨ (statementListToCondition a (cc :=: false) f)

    statementListToCondition : Condition -> Condition -> List StatementType -> Condition
    statementListToCondition a1 a2 [] = a2
    statementListToCondition a1 a2 (x ∷ xs) = let a3 = (replaceVarsInNewCondition a1 (statementToCondition a1 x)) in statementListToCondition (a1 ∧ a3) (a2 ∧ a3) xs

statementListToHoareTriplets : Condition -> List StatementType -> List (HoareTriplet (List String))
statementListToHoareTriplets a [] = (⟪ a ⟫ (statementToString EmptyStatement) ⟪ false ⟫) ∷ [] -- Should not come here
statementListToHoareTriplets a (x ∷ []) = let pC = (a ∧ replaceVarsInNewCondition a (statementToCondition a x)) in 
                                    ⟪ a ⟫ (statementToString x) ⟪ pC ⟫ ∷ []
statementListToHoareTriplets a (x ∷ xs) = let pC = (a ∧ replaceVarsInNewCondition a (statementToCondition a x)) in 
                                    ⟪ a ⟫ (statementToString x) ⟪ pC ⟫ ∷ (statementListToHoareTriplets pC xs)

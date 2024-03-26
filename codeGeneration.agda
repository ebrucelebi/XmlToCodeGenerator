{-# OPTIONS --safe #-}

module codeGeneration where

open import utility
open import IMODEDataTypes
open import ModelDAG
open import createDAG
open import checkProject
open import CodeRepresentation
open import HoareLogic

open import Data.String
open import Data.Maybe
open import Data.Bool hiding (_∧_; _∨_)
open import Data.Product
open import Data.List hiding (concat; _++_)
open import Data.Fin hiding (join; _+_; _-_;_>_; _<_)
open import Data.Nat hiding (_+_; _*_; _^_; _>_; _<_)
open import Data.Graph.Acyclic hiding(weaken)
open import Agda.Builtin.Equality

record GeneratedFile : Set where
    constructor File
    field
        fileName : String
        content : List String

data CodeGenerationResult : Set where
    Success : List GeneratedFile -> CodeGenerationResult
    GenerationError : String -> CodeGenerationResult
    CheckError : List String -> CodeGenerationResult

data CodeSection : Set where
    Identifier : CodeSection
    Main : CodeSection
    Declaration : CodeSection

getOutputType : ∀ {n} -> ℕ -> Model -> ModelDAG n -> Type
getOutputType _ _ ∅ = iNone
getOutputType i m (context (InputInstance _ sourceId) edges & dag) with findModelElementInModelWithID m sourceId
... | just (Input _ _ type) = type
... | _ = iNone
getOutputType i m (context (OutputInstance _ sourceId) edges & dag) with findModelElementInModelWithID m sourceId
... | just (Output _ _ type) = type
... | _ = iNone
getOutputType (suc i) m (context (Addition _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType (suc i) m (context (Modulo _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType (suc i) m (context (Multiplication _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType (suc i) m (context (NumericCast _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e) -- todo: Fix after adding the cast type
getOutputType (suc i) m (context (PolymorphicDivision _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType (suc i) m (context (Subtraction _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType (suc i) m (context (UnaryMinus _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType i m (context (LogicalAnd _) edges & dag) = iBool
getOutputType i m (context (LogicalNot _) edges & dag) = iBool
getOutputType i m (context (LogicalOr _) edges & dag) = iBool
getOutputType i m (context (LogicalSharp _) edges & dag) = iBool
getOutputType i m (context (LogicalXor _) edges & dag) = iBool
getOutputType (suc i) m (context (BitwiseAnd _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType (suc i) m (context (BitwiseNot _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType (suc i) m (context (BitwiseOr _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType (suc i) m (context (BitwiseXor _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType (suc i) m (context (LeftShift _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType (suc i) m (context (RightShift _) (e ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType i m (context (Different _) edges & dag) = iBool
getOutputType i m (context (Equal _) edges & dag) = iBool
getOutputType i m (context (GreaterThanEqual _) edges & dag) = iBool
getOutputType i m (context (LessThanEqual _) edges & dag) = iBool
getOutputType i m (context (StrictlyGreaterThan _) edges & dag) = iBool
getOutputType i m (context (StrictlyLessThan _) edges & dag) = iBool
getOutputType (suc i) m (context (If _) (e1 ∷ e2 ∷ es) & dag) = getOutputType i m (getEdgeDestination dag e2) -- e1 is condition
getOutputType _ _ _ = iNone

mutual
    generateEdges : ∀ {n} -> Project -> Model -> CodeSection -> List (ModelElement × Fin n) -> ModelDAG n -> List String
    generateEdges _ _ _ [] _ = []
    generateEdges _ _ _ _ ∅ = []
    generateEdges p m section (e ∷ xs) (c & dag) with generateEdges p m section xs (c & dag)
    generateEdges p m section (e ∷ xs) (c & dag) | res1 with e
    generateEdges p m section (e ∷ xs) (c & dag) | res1 | (_ , zero) with generateModelElement p m section c dag
    generateEdges p m section (e ∷ xs) (c & dag) | res1 | (_ , zero) | res2 = concatenateTwoList res1 res2
    generateEdges p m section (e ∷ xs) (c & dag) | res1 | (me , (suc f)) with generateEdges p m section ((me , f) ∷ []) dag
    generateEdges p m section (e ∷ xs) (c & dag) | res1 | (me , (suc f)) | res2 = concatenateTwoList res1 res2

    generateIdentifierEdge : ∀ {n} -> Project -> Model -> ModelElement × Fin n -> ModelDAG n -> String
    generateIdentifierEdge p m e dag with generateEdges p m Identifier (e ∷ []) dag
    ... | x ∷ [] = x
    ... | _ = ""

    generateIdentifierAtEdge : ∀ {n} -> Project -> Model -> List (ModelElement × Fin n) -> ℕ -> ModelDAG n -> String
    generateIdentifierAtEdge _ _ [] _ _ = ""
    generateIdentifierAtEdge p m (e ∷ es) zero dag = generateIdentifierEdge p m e dag
    generateIdentifierAtEdge p m (e ∷ es) (suc n) dag = generateIdentifierAtEdge p m es n dag
    
    generateIdentifierEdges : ∀ {n} -> Project -> Model -> List (ModelElement × Fin n) -> ModelDAG n -> List String
    generateIdentifierEdges _ _ [] _ = []
    generateIdentifierEdges p m (e ∷ es) dag = (generateIdentifierEdge p m e dag) ∷ (generateIdentifierEdges p m es dag)

    generateIdentifierContext : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> String
    generateIdentifierContext p m c dag with generateModelElement p m Identifier c dag
    ... | x ∷ [] = x
    ... | _ = ""
    
    generateInputMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateInputMain _ _ _ _ = []

    generateOutputMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateOutputMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                              (Variable (generateIdentifierAtEdge p m edges 0 dag)) ∷ []

    generateAdditionMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateAdditionMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                (joinToExpression (generateIdentifierEdges p m edges dag) Addition) ∷ []

    generateMultiplicationMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateMultiplicationMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                      (joinToExpression (generateIdentifierEdges p m edges dag) Multiplication) ∷ []

    -- TODO: Add cast type
    generateNumericCastMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateNumericCastMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                   (Variable (generateIdentifierAtEdge p m edges 0 dag)) ∷ []

    generatePolymorphicDivisionMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generatePolymorphicDivisionMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                           (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                                       Division
                                                                                       (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []

    generateSubtractionMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateSubtractionMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                   (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                               Subtraction
                                                                               (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []
                                  
    generateUnaryMinusMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateUnaryMinusMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                  (RightExpression Minus
                                                                                   (Variable (generateIdentifierAtEdge p m edges 0 dag))) ∷ []

    generateLogicalAndMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateLogicalAndMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                  (joinToExpression (generateIdentifierEdges p m edges dag) LogicalAnd) ∷ []

    generateLogicalNorMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateLogicalNorMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                  (RightExpression LogicalNot
                                                                                   (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                                               LogicalOr
                                                                                               (Variable (generateIdentifierAtEdge p m edges 1 dag)))) ∷ []
                                  
    generateLogicalNotMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateLogicalNotMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                  (RightExpression LogicalNot
                                                                                   (Variable (generateIdentifierAtEdge p m edges 0 dag))) ∷ []

    generateLogicalOrMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateLogicalOrMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                 (joinToExpression (generateIdentifierEdges p m edges dag) LogicalOr) ∷ []

    generateLogicalSharpMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateLogicalSharpMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                    (Expression (joinToExpression (generateIdentifierEdges p m edges dag) Addition)
                                                                                LessThanEqual
                                                                                (Variable "1")) ∷ []

    generateLogicalXorMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateLogicalXorMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                  (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                              LogicalXor
                                                                              (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []

    generateBitwiseAndMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateBitwiseAndMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                  (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                              BitwiseAnd
                                                                              (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []

    generateBitwiseNotMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateBitwiseNotMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                  (RightExpression BitwiseNot
                                                                                   (Variable (generateIdentifierAtEdge p m edges 0 dag))) ∷ []

    generateBitwiseOrMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateBitwiseOrMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                 (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                             BitwiseOr
                                                                             (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []

    generateBitwiseXorMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateBitwiseXorMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                  (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                              BitwiseXor
                                                                              (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []

    generateLeftShiftMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateLeftShiftMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                 (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                             LeftShift
                                                                             (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []

    generateRightShiftMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateRightShiftMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                  (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                              RightShift
                                                                              (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []

    -- TODO: After creating types header with compare functions, fix different code.
    generateDifferentMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateDifferentMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                 (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                             Different
                                                                             (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []

    -- TODO: After creating types header with compare functions, fix equal code.
    generateEqualMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateEqualMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                             (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                         Equal
                                                                         (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []

    generateGreaterThanEqualMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateGreaterThanEqualMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                        (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                                    GreaterThanEqual
                                                                                    (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []
                                  
    generateLessThanEqualMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateLessThanEqualMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                     (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                                 LessThanEqual
                                                                                 (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []
                                  
    generateStrictlyGreaterThanMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateStrictlyGreaterThanMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                           (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                                       StrictlyGreaterThan
                                                                                       (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []
                                  
    generateStrictlyLessThanMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateStrictlyLessThanMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                        (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                                    StrictlyLessThan
                                                                                    (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []
                                  
    generateIfMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateIfMain p m (context me edges) dag = IfStatement (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                            ((Statement (generateIdentifierContext p m (context me edges) dag)
                                                                        (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ [])
                                                            ((Statement (generateIdentifierContext p m (context me edges) dag)
                                                                        (Variable (generateIdentifierAtEdge p m edges 2 dag))) ∷ []) ∷ []

    generateModelElementMain : ∀ {n} -> ModelElement -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateModelElementMain (OutputInstance _ _) p m c dag = generateOutputMain p m c dag
    generateModelElementMain (Addition _) p m c dag = generateAdditionMain p m c dag
    generateModelElementMain (Multiplication _) p m c dag = generateMultiplicationMain p m c dag
    generateModelElementMain (InputInstance _ _) p m c dag = generateInputMain p m c dag
    generateModelElementMain (NumericCast _) p m c dag = generateNumericCastMain p m c dag
    generateModelElementMain (PolymorphicDivision _) p m c dag = generatePolymorphicDivisionMain p m c dag
    generateModelElementMain (Subtraction _) p m c dag = generateSubtractionMain p m c dag
    generateModelElementMain (UnaryMinus _) p m c dag = generateUnaryMinusMain p m c dag
    generateModelElementMain (LogicalAnd _) p m c dag = generateLogicalAndMain p m c dag
    generateModelElementMain (LogicalNor _) p m c dag = generateLogicalNorMain p m c dag
    generateModelElementMain (LogicalNot _) p m c dag = generateLogicalNotMain p m c dag
    generateModelElementMain (LogicalOr _) p m c dag = generateLogicalOrMain p m c dag
    generateModelElementMain (LogicalSharp _) p m c dag = generateLogicalSharpMain p m c dag
    generateModelElementMain (LogicalXor _) p m c dag = generateLogicalXorMain p m c dag
    generateModelElementMain (BitwiseAnd _) p m c dag = generateBitwiseAndMain p m c dag
    generateModelElementMain (BitwiseNot _) p m c dag = generateBitwiseNotMain p m c dag
    generateModelElementMain (BitwiseOr _) p m c dag = generateBitwiseOrMain p m c dag
    generateModelElementMain (BitwiseXor _) p m c dag = generateBitwiseXorMain p m c dag
    generateModelElementMain (LeftShift _) p m c dag = generateLeftShiftMain p m c dag
    generateModelElementMain (RightShift _) p m c dag = generateRightShiftMain p m c dag
    generateModelElementMain (Different _) p m c dag = generateDifferentMain p m c dag
    generateModelElementMain (Equal _) p m c dag = generateEqualMain p m c dag
    generateModelElementMain (GreaterThanEqual _) p m c dag = generateGreaterThanEqualMain p m c dag
    generateModelElementMain (LessThanEqual _) p m c dag = generateLessThanEqualMain p m c dag
    generateModelElementMain (StrictlyGreaterThan _) p m c dag = generateStrictlyGreaterThanMain p m c dag
    generateModelElementMain (StrictlyLessThan _) p m c dag = generateStrictlyLessThanMain p m c dag
    generateModelElementMain (If _) p m c dag = generateIfMain p m c dag
    generateModelElementMain _ p m c dag = []

    generateModelElement : ∀ {n} -> Project -> Model -> CodeSection -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateModelElement    p m Identifier  (context me edges)                   dag = (getModelElementName me) ∷ []
    generateModelElement{n} p m Declaration (context (InputInstance _ _) edges)  dag = []
    generateModelElement{n} p m Declaration (context (OutputInstance _ _) edges) dag = []
    generateModelElement{n} p m Declaration c                                    dag = (getStringFromType (getOutputType n m (c & dag)) ++ " " ++ (generateIdentifierContext p m c dag) ++ ";") ∷ []
    generateModelElement    p m Main        (context me edges)                   dag = statementListToString (generateModelElementMain me p m (context me edges) dag)

-- Go over DAG and call generate section code for the model element.
-- DAG is already ordered so that all necessary codes for a model element are generated before its own code.
generateModelElements : ∀ {n} -> Project -> Model -> CodeSection -> ModelDAG n -> List String
generateModelElements _ _ _ ∅ = []
generateModelElements p m section (c & dag) = concatenateTwoList (generateModelElements p m section dag) (generateModelElement p m section c dag) 

generateModelElementsStatementList : ∀ {n} -> Project -> Model -> ModelDAG n -> List StatementType
generateModelElementsStatementList _ _ ∅ = []
generateModelElementsStatementList p m ((context me edges) & dag) = concatenateTwoList (generateModelElementsStatementList p m dag) (generateModelElementMain me p m (context me edges) dag)

generateModelSource : ∀ {n} -> Project -> Model -> String -> ModelDAG n -> GeneratedFile
generateModelSource p m n dag with generateModelElements p m Main dag | generateModelElements p m Declaration dag
... | mainContent | declarationContent = File (n ++ ".c") (
    ("#include \"" ++ n ++ ".h\"") ∷ "" ∷
    ("void " ++ n ++ "Main(i_" ++ n ++ "* inputs, o_" ++ n ++ "* outputs)") ∷
    (encapsulateBraces (declarationContent Data.List.++ [""] Data.List.++ mainContent))
    )

-- Create DAG and start the code generation for the model elements in the order.
generateModel : Project -> Model -> CodeGenerationResult
generateModel p (Operation n ins outs sms) with (createDAG (Operation n ins outs sms))
... | nothing = GenerationError ("Could not generate DAG for" ++ n)
... | just dag = Success (generateModelSource p (Operation n ins outs sms) n dag ∷ [])

getInputsCondition : List ModelElement -> Condition
getInputsCondition [] = true
getInputsCondition ((Input n _ _) ∷ []) = Defined (var n)
getInputsCondition ((Input n _ _) ∷ xs) = (Defined (var n)) ∧ getInputsCondition xs
getInputsCondition _ = false

getIOVars : List ModelElement -> List Var
getIOVars ((Output n _ _) ∷ xs) = (var n) ∷ getIOVars xs
getIOVars ((Input n _ _) ∷ xs) = (var n) ∷ getIOVars xs
getIOVars _ = []

generateModelCodeCondition : Project -> Model -> Maybe Condition
generateModelCodeCondition p (Operation n ins outs sms) with (createDAG (Operation n ins outs sms))
... | nothing = nothing
... | just dag = just (
    weaken 
        (statementListToCondition (getInputsCondition ins) (getInputsCondition ins)
                                  (generateModelElementsStatementList p (Operation n ins outs sms) dag))
        (getIOVars (ins Data.List.++ outs)))

generateModelCodeHoareTriplets : Project -> Model -> Maybe (List (HoareTriplet (List String)))
generateModelCodeHoareTriplets p (Operation n ins outs sms) with (createDAG (Operation n ins outs sms))
... | nothing = nothing
... | just dag = just (statementListToHoareTriplets (getInputsCondition ins) (generateModelElementsStatementList p (Operation n ins outs sms) dag))


generateAdditionAnnotation : List String -> Annotation
generateAdditionAnnotation [] = var ""
generateAdditionAnnotation (x ∷ []) = var x
generateAdditionAnnotation (x ∷ xs) = (var x) + generateAdditionAnnotation xs

generateMultiplicationAnnotation : List String -> Annotation
generateMultiplicationAnnotation [] = var ""
generateMultiplicationAnnotation (x ∷ []) = var x
generateMultiplicationAnnotation (x ∷ xs) = (var x) * generateMultiplicationAnnotation xs

generateModelElementCondition : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> Condition
generateModelElementCondition p m (context (Addition (Properties n _ _ _ _)) edges) dag =
    (var n) :=: generateAdditionAnnotation (generateIdentifierEdges p m edges dag)
generateModelElementCondition p m (context (Multiplication (Properties n _ _ _ _)) edges) dag =
    (var n) :=: generateMultiplicationAnnotation (generateIdentifierEdges p m edges dag)
generateModelElementCondition p m (context (Subtraction (Properties n _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) - (var (generateIdentifierAtEdge p m edges 1 dag))
generateModelElementCondition p m (context (StrictlyGreaterThan (Properties n _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) > (var (generateIdentifierAtEdge p m edges 1 dag))
generateModelElementCondition p m (context (OutputInstance (Properties n _ _ _ _) _) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag))
generateModelElementCondition p m (context (If (Properties n _ _ _ _)) edges) dag = let cond = (var (generateIdentifierAtEdge p m edges 0 dag)) in
    (((cond :=: true) ∧ (var n) :=: var (generateIdentifierAtEdge p m edges 1 dag)) ∨
     ((cond :=: false) ∧ (var n) :=: var (generateIdentifierAtEdge p m edges 2 dag)))
generateModelElementCondition _ _ _ _ = false

generateCondition : ∀ {n} -> Project -> Model -> ModelDAG n -> Condition
generateCondition p m ∅ = true
generateCondition p m ((context (InputInstance (Properties n _ _ _ _) _) edges) & dag) = generateCondition p m dag ∧ Defined (var n)
generateCondition p m ((context me edges) & dag) = let c = generateCondition p m dag in
    c ∧ replaceVarsInNewCondition c (generateModelElementCondition p m (context me edges) dag)

generateModelDAGCondition : Project -> Model -> Maybe Condition
generateModelDAGCondition p (Operation n ins outs sms) with (createDAG (Operation n ins outs sms))
... | nothing = nothing
... | just dag = just (weaken
    (generateCondition p (Operation n ins outs sms) dag) (getIOVars (ins Data.List.++ outs)))

-- To generate a code for the project, code generation should have a root model to start.
generateCode : Project -> String -> CodeGenerationResult
generateCode p n with findModelInProjectWithName p n
... | nothing = GenerationError ("Could not find the root model " ++ n)
... | just m = generateModel p m

checkAndGenerateCode : Maybe Project -> String -> CodeGenerationResult
checkAndGenerateCode p n with checkProject p | p
... | Success | just pro = (generateCode pro n)
... | Success | nothing = GenerationError ("There is no project.")
... | Error errors | _ = CheckError errors

denemeGen : CodeGenerationResult
denemeGen = generateModel (project "" [] [] [] []) doubleOutputModel

denemeGen2 : CodeGenerationResult
denemeGen2 = generateModel (project "" [] [] [] []) ifExample

denemeHoare : Maybe (List (HoareTriplet (List String)))
denemeHoare = generateModelCodeHoareTriplets (project "" [] [] [] []) doubleOutputModel

denemeCodeCond : Maybe Condition
denemeCodeCond = generateModelCodeCondition (project "" [] [] [] []) doubleOutputModel

denemeCodeCond2 : Maybe Condition
denemeCodeCond2 = generateModelCodeCondition (project "" [] [] [] []) ifExample

denemeHoare2 : Maybe (List (HoareTriplet (List String)))
denemeHoare2 = generateModelCodeHoareTriplets (project "" [] [] [] []) ifExample

denemeDAGCond : Maybe Condition
denemeDAGCond = generateModelDAGCondition (project "" [] [] [] []) doubleOutputModel

denemeDAGCond2 : Maybe Condition
denemeDAGCond2 = generateModelDAGCondition (project "" [] [] [] []) ifExample

checkResult : Bool
checkResult with denemeCodeCond | denemeDAGCond
... | just c1 | just c2 = c1 ≟C c2
... | _ | _ = false

checkResult2 : Bool
checkResult2 with denemeCodeCond2 | denemeDAGCond2
... | just c1 | just c2 = c1 ≟C c2
... | _ | _ = false

testHoare : checkResult ≡ true
testHoare = refl

testHoare2 : checkResult2 ≡ true
testHoare2 = refl
 
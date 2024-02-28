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
open import Data.Bool hiding (_∧_)
open import Data.Product
open import Data.List hiding (concat; _++_)
open import Data.Fin hiding (join; _+_)
open import Data.Nat hiding (_+_; _*_; _^_; _>_; _<_)
open import Data.Graph.Acyclic

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
    generateModelElementMain _ p m c dag = []

    generateModelElement : ∀ {n} -> Project -> Model -> CodeSection -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateModelElement    p m Identifier  (context me edges) dag = (getModelElementName me) ∷ []
    generateModelElement{n} p m Declaration c                  dag = (getStringFromType (getOutputType n m (c & dag)) ++ " " ++ (generateIdentifierContext p m c dag) ++ ";") ∷ []
    generateModelElement    p m Main        (context me edges) dag = statementListToString (generateModelElementMain me p m (context me edges) dag)

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

getInputsAnnotation : List ModelElement -> Annotation
getInputsAnnotation [] = true
getInputsAnnotation ((Input n _ _) ∷ []) = Defined (var n)
getInputsAnnotation ((Input n _ _) ∷ xs) = (Defined (var n)) ∧ getInputsAnnotation xs
getInputsAnnotation _ = false

generateModelCodeAnnotation : Project -> Model -> Maybe Annotation
generateModelCodeAnnotation p (Operation n ins outs sms) with (createDAG (Operation n ins outs sms))
... | nothing = nothing
... | just dag = just (statementListToAnnotation (getInputsAnnotation ins) (generateModelElementsStatementList p (Operation n ins outs sms) dag))

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

denemeAnn : Maybe Annotation
denemeAnn = generateModelCodeAnnotation (project "" [] [] [] []) doubleOutputModel

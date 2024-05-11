{-# OPTIONS --safe #-}

module codeGeneration where

open import utility
open import IMODEDataTypes hiding (Constant)
open import ModelDAG
open import createDAG
open import checkProject
open import CodeRepresentation
open import HoareLogic

open import Data.String hiding (_==_; _<_)
open import Data.Maybe
open import Data.Bool hiding (_∧_; _∨_; _<_)
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
    VerifyError : CodeGenerationResult

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
getOutputType (suc i) m (context (Previous (Properties a b c1 d f ("" ∷ [])) _) (e ∷ []) & dag) = getOutputType i m (getEdgeDestination dag e)
getOutputType (suc i) m (context (Previous (Properties a b c1 d f (s ∷ [])) _) (e1 ∷ e2 ∷ []) & dag) = getOutputType i m (getEdgeDestination dag e2)
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

    generateModuloMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateModuloMain p m (context me edges) dag = Statement (generateIdentifierContext p m (context me edges) dag)
                                                                (Expression (Variable (generateIdentifierAtEdge p m edges 0 dag))
                                                                            Modulo
                                                                            (Variable (generateIdentifierAtEdge p m edges 1 dag))) ∷ []

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

    generatePreviousMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generatePreviousMain p m (context (Previous (Properties a b c d f ("" ∷ [])) (initValue ∷ [])) []) dag = let me = (Previous (Properties a b c d f ("" ∷ [])) (initValue ∷ [])) in
        IfStatement (Variable "isInitialCycle")
                    ((Statement (generateIdentifierContext p m (context me []) dag)
                                (Constant initValue)) ∷ [])
                    ((Statement (generateIdentifierContext p m (context me []) dag)
                                (Variable ((generateIdentifierContext p m (context me []) dag) ++ "_mem"))) ∷ [])
                                ∷ []
    generatePreviousMain p m (context (Previous (Properties a b c d f ("" ∷ [])) (initValue ∷ [])) (e1 ∷ [])) dag = let me = (Previous (Properties a b c d f ("" ∷ [])) (initValue ∷ [])) in
        Statement ((generateIdentifierContext p m (context me (e1 ∷ [])) dag) ++ "_mem")
                  (Variable (generateIdentifierAtEdge p m (e1 ∷ []) 0 dag))
                                ∷ []
    generatePreviousMain p m (context (Previous (Properties a b c d f (s ∷ [])) (initValue ∷ [])) (e ∷ [])) dag = let me = (Previous (Properties a b c d f (s ∷ [])) (initValue ∷ [])) in
        IfStatement (Variable "isInitialCycle")
                    ((Statement (generateIdentifierContext p m (context me []) dag)
                                (Variable (generateIdentifierAtEdge p m (e ∷ []) 0 dag))) ∷ [])
                    ((Statement (generateIdentifierContext p m (context me []) dag)
                                (Variable ((generateIdentifierContext p m (context me []) dag) ++ "_mem"))) ∷ [])
                                ∷ []
    generatePreviousMain p m (context (Previous (Properties a b c d f (s ∷ [])) (initValue ∷ [])) (e1 ∷ e2 ∷ [])) dag = let me = (Previous (Properties a b c d f (s ∷ [])) (initValue ∷ [])) in
        Statement ((generateIdentifierContext p m (context me (e1 ∷ e2 ∷ [])) dag) ++ "_mem")
                  (Variable (generateIdentifierAtEdge p m (e1 ∷ e2 ∷ []) 1 dag))
                                ∷ []
    generatePreviousMain _ _ _ _ = []

    generateTextualMain : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateTextualMain p m (context (Textual pro text) edges) dag = Statement (generateIdentifierContext p m (context (Textual pro text) edges) dag)
                                                              (Constant text) ∷ []
    generateTextualMain _ _ _ _ = []

    generateModelElementMain : ∀ {n} -> ModelElement -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> List StatementType
    generateModelElementMain (OutputInstance _ _) p m c dag = generateOutputMain p m c dag
    generateModelElementMain (Addition _) p m c dag = generateAdditionMain p m c dag
    generateModelElementMain (Modulo _) p m c dag = generateModuloMain p m c dag
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
    generateModelElementMain (Previous _ _) p m c dag = generatePreviousMain p m c dag
    generateModelElementMain (Textual _ _) p m c dag = generateTextualMain p m c dag
    generateModelElementMain _ p m c dag = []

    generateModelElement : ∀ {n} -> Project -> Model -> CodeSection -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateModelElement p m Identifier  (context me edges)                   dag = (getModelElementName me) ∷ []
    generateModelElement p m Declaration (context (InputInstance _ _) edges)  dag = []
    generateModelElement p m Declaration (context (OutputInstance _ _) edges) dag = []
    generateModelElement{n} p m Declaration c dag with getOutputType n m (c & dag)
    generateModelElement{n} p m Declaration c dag | iNone = []
    generateModelElement{n} p m Declaration c dag | t = ((getStringFromType t) ++ " " ++ (generateIdentifierContext p m c dag) ++ ";") ∷ []
    generateModelElement p m Main        (context me edges)                   dag = statementListToString (generateModelElementMain me p m (context me edges) dag)

-- Go over DAG and call generate section code for the model element.
-- DAG is already ordered so that all necessary codes for a model element are generated before its own code.
generateModelElements : ∀ {n} -> Project -> Model -> CodeSection -> ModelDAG n -> List ModelElement -> List String
generateModelElements _ _ _ ∅ _ = []
generateModelElements p m section ((context me edges) & dag) seen with containsModelElement seen me
generateModelElements p m section (c & dag) seen                    | false = concatenateTwoList (generateModelElements p m section dag seen) (generateModelElement p m section c dag)
generateModelElements p m section ((context me edges) & dag) seen   | true with me | edges
generateModelElements p m section (c & dag) seen                    | true | (Previous (Properties a b c1 d f ("" ∷ [])) _) | (e ∷ []) = 
                                                concatenateTwoList (generateModelElements p m section dag seen) (generateModelElement p m section c dag)
generateModelElements p m section (c & dag) seen                    | true | (Previous (Properties a b c1 d f (s ∷ [])) _) | (e1 ∷ e2 ∷ []) = 
                                                concatenateTwoList (generateModelElements p m section dag seen) (generateModelElement p m section c dag)
generateModelElements p m section (c & dag) seen                    | true | _ | _ = (generateModelElements p m section dag seen)

generateModelElementsDAGs : ∀ {n} -> Project -> Model -> CodeSection -> List (ModelDAG n) -> List ModelElement -> List String
generateModelElementsDAGs _ _ _ [] _ = []
generateModelElementsDAGs p m section (dag ∷ dags) seen = concatenateTwoList
                                                            (generateModelElements p m section dag seen)
                                                            (generateModelElementsDAGs p m section dags (seen Data.List.++ (DAGToList dag)))

generateModelElementsStatementList : ∀ {n} -> Project -> Model -> ModelDAG n -> List ModelElement -> List StatementType
generateModelElementsStatementList _ _ ∅ _ = []
generateModelElementsStatementList p m ((context me edges) & dag) seen with containsModelElement seen me
generateModelElementsStatementList p m ((context me edges) & dag) seen   | false = concatenateTwoList
                                                                        (generateModelElementsStatementList p m dag seen)
                                                                        (generateModelElementMain me p m (context me edges) dag)
generateModelElementsStatementList p m ((context me edges) & dag) seen   | true with me | edges
generateModelElementsStatementList p m ((context me edges) & dag) seen   | true | (Previous (Properties a b c1 d f ("" ∷ [])) _) | (e ∷ []) = 
                                                concatenateTwoList
                                                    (generateModelElementsStatementList p m dag seen)
                                                    (generateModelElementMain me p m (context me edges) dag)
generateModelElementsStatementList p m ((context me edges) & dag) seen   | true | (Previous (Properties a b c1 d f (s ∷ [])) _) | (e1 ∷ e2 ∷ []) = 
                                                concatenateTwoList
                                                    (generateModelElementsStatementList p m dag seen)
                                                    (generateModelElementMain me p m (context me edges) dag)
generateModelElementsStatementList p m (c & dag) seen                    | true | _ | _ = (generateModelElementsStatementList p m dag seen)
                                                                        
generateModelElementsStatementListDAGs : ∀ {n} -> Project -> Model -> List (ModelDAG n) -> List ModelElement -> List StatementType
generateModelElementsStatementListDAGs _ _ [] _ = []
generateModelElementsStatementListDAGs p m (dag ∷ dags) seen = concatenateTwoList
                                                            (generateModelElementsStatementList p m dag seen)
                                                            (generateModelElementsStatementListDAGs p m dags (seen Data.List.++ (DAGToList dag)))

generateModelSource : ∀ {n} -> Project -> Model -> String -> List (ModelDAG n) -> GeneratedFile
generateModelSource p m n dags with generateModelElementsDAGs p m Main dags [] | generateModelElementsDAGs p m Declaration dags []
... | mainContent | declarationContent = File (n ++ ".c") (
    ("#include \"" ++ n ++ ".h\"") ∷ "" ∷
    ("void " ++ n ++ "Main(i_" ++ n ++ "* inputs, o_" ++ n ++ "* outputs)") ∷
    (encapsulateBraces (declarationContent Data.List.++ [""] Data.List.++ mainContent))
    )

-- Create DAG and start the code generation for the model elements in the order.
generateModel : Project -> Model -> CodeGenerationResult
generateModel p (Operation n ins outs sms) with (createDAG (Operation n ins outs sms))
... | nothing = GenerationError ("Could not generate DAG for " ++ n)
... | just dags = Success (generateModelSource p (Operation n ins outs sms) n dags ∷ [])

getInputsCondition : List ModelElement -> Condition
getInputsCondition [] = true
getInputsCondition ((Input n _ _) ∷ []) = Defined (var n)
getInputsCondition ((Input n _ _) ∷ xs) = (Defined (var n)) ∧ getInputsCondition xs
getInputsCondition _ = false

getModelElementVars : List ModelElement -> List Var
getModelElementVars [] = []
getModelElementVars ((Previous (Properties n _ _ _ _ _) _) ∷ xs) = (var n) ∷ (var (n ++ "_mem")) ∷ getModelElementVars xs
getModelElementVars (me ∷ xs) = (var (getModelElementName me)) ∷ getModelElementVars xs

generateModelCodeCondition : Project -> Model -> Condition -> Maybe Condition
generateModelCodeCondition p (Operation n ins outs sms) preC with (createDAG (Operation n ins outs sms))
... | nothing = nothing
... | just dags = just (
     weaken 
        (statementListToCondition preC preC
                                  (generateModelElementsStatementListDAGs p (Operation n ins outs sms) dags []))
        ((var "isInitialCycle") ∷ (getModelElementVars (DAGsToListReverse dags)))
        ((var "isInitialCycle") ∷ (getModelElementVars (ins Data.List.++ outs)))
        )

generateModelCodeHoareTriplets : Project -> Model -> Maybe (List (HoareTriplet (List String)))
generateModelCodeHoareTriplets p (Operation n ins outs sms) with (createDAG (Operation n ins outs sms))
... | nothing = nothing
... | just dags = just (statementListToHoareTriplets (Defined (var "isInitialCycle") ∧ (getInputsCondition ins))
                                                     (generateModelElementsStatementListDAGs p (Operation n ins outs sms) dags []))


generateAdditionAnnotation : List String -> Annotation
generateAdditionAnnotation [] = var ""
generateAdditionAnnotation (x ∷ []) = var x
generateAdditionAnnotation (x ∷ xs) = (var x) + generateAdditionAnnotation xs

generateMultiplicationAnnotation : List String -> Annotation
generateMultiplicationAnnotation [] = var ""
generateMultiplicationAnnotation (x ∷ []) = var x
generateMultiplicationAnnotation (x ∷ xs) = (var x) * generateMultiplicationAnnotation xs

generateLogicalAndAnnotation : List String -> Annotation
generateLogicalAndAnnotation [] = var ""
generateLogicalAndAnnotation (x ∷ []) = var x
generateLogicalAndAnnotation (x ∷ xs) = (var x) && generateLogicalAndAnnotation xs

generateLogicalOrAnnotation : List String -> Annotation
generateLogicalOrAnnotation [] = var ""
generateLogicalOrAnnotation (x ∷ []) = var x
generateLogicalOrAnnotation (x ∷ xs) = (var x) || generateLogicalOrAnnotation xs

generateBitwiseAndAnnotation : List String -> Annotation
generateBitwiseAndAnnotation [] = var ""
generateBitwiseAndAnnotation (x ∷ []) = var x
generateBitwiseAndAnnotation (x ∷ xs) = (var x) & generateBitwiseAndAnnotation xs

generateBitwiseOrAnnotation : List String -> Annotation
generateBitwiseOrAnnotation [] = var ""
generateBitwiseOrAnnotation (x ∷ []) = var x
generateBitwiseOrAnnotation (x ∷ xs) = (var x) |b generateBitwiseOrAnnotation xs

generateModelElementCondition : ∀ {n} -> Project -> Model -> Context ModelElement ModelElement n -> ModelDAG n -> Condition
generateModelElementCondition p m (context (InputInstance (Properties n _ _ _ _ _) _) edges) dag =
    Defined (var n)

generateModelElementCondition p m (context (OutputInstance (Properties n _ _ _ _ _) _) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag))

generateModelElementCondition p m (context (Addition (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: generateAdditionAnnotation (generateIdentifierEdges p m edges dag)

generateModelElementCondition p m (context (Modulo (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) % (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (Multiplication (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: generateMultiplicationAnnotation (generateIdentifierEdges p m edges dag)

generateModelElementCondition p m (context (NumericCast (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag))

generateModelElementCondition p m (context (PolymorphicDivision (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) - (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (Subtraction (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) - (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (UnaryMinus (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: - (var (generateIdentifierAtEdge p m edges 0 dag))

generateModelElementCondition p m (context (LogicalAnd (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: generateLogicalAndAnnotation (generateIdentifierEdges p m edges dag)

generateModelElementCondition p m (context (LogicalNor (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: ! ((var (generateIdentifierAtEdge p m edges 0 dag)) || (var (generateIdentifierAtEdge p m edges 1 dag)))

generateModelElementCondition p m (context (LogicalNot (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: ! (var (generateIdentifierAtEdge p m edges 0 dag))

generateModelElementCondition p m (context (LogicalOr (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: generateLogicalOrAnnotation (generateIdentifierEdges p m edges dag)

generateModelElementCondition p m (context (LogicalSharp (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (generateAdditionAnnotation (generateIdentifierEdges p m edges dag)) <= (const "1")

generateModelElementCondition p m (context (LogicalXor (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) ^ (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (BitwiseAnd (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: generateBitwiseAndAnnotation (generateIdentifierEdges p m edges dag)

generateModelElementCondition p m (context (BitwiseNot (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: ~ (var (generateIdentifierAtEdge p m edges 0 dag))

generateModelElementCondition p m (context (BitwiseOr (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: generateBitwiseOrAnnotation (generateIdentifierEdges p m edges dag)

generateModelElementCondition p m (context (BitwiseXor (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) ^ (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (LeftShift (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) << (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (RightShift (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) >> (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (Different (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) != (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (Equal (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) == (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (GreaterThanEqual (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) >= (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (LessThanEqual (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) <= (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (StrictlyGreaterThan (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) > (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (StrictlyLessThan (Properties n _ _ _ _ _)) edges) dag =
    (var n) :=: (var (generateIdentifierAtEdge p m edges 0 dag)) < (var (generateIdentifierAtEdge p m edges 1 dag))

generateModelElementCondition p m (context (If (Properties n _ _ _ _ _)) edges) dag = let cond = (var (generateIdentifierAtEdge p m edges 0 dag)) in
    (((cond :=: true) ∧ (var n) :=: var (generateIdentifierAtEdge p m edges 1 dag)) ∨
     ((cond :=: false) ∧ (var n) :=: var (generateIdentifierAtEdge p m edges 2 dag)))

generateModelElementCondition p m (context (Previous (Properties n _ _ _ _ ("" ∷ [])) (initValue ∷ [])) []) dag =
    ((((var "isInitialCycle") :=: true) ∧ (var n) :=: (const initValue)) ∨
     (((var "isInitialCycle") :=: false) ∧ (var n) :=: (var (n ++ "_mem"))))

generateModelElementCondition p m (context (Previous (Properties n _ _ _ _ ("" ∷ [])) (initValue ∷ [])) (e1 ∷ [])) dag =
    (var (n ++ "_mem")) :=: var (generateIdentifierAtEdge p m (e1 ∷ []) 0 dag)

generateModelElementCondition p m (context (Previous (Properties n _ _ _ _ (s ∷ [])) (initValue ∷ [])) (e ∷ [])) dag =
    ((((var "isInitialCycle") :=: true) ∧ (var n) :=: (var (generateIdentifierAtEdge p m (e ∷ []) 0 dag))) ∨
     (((var "isInitialCycle") :=: false) ∧ (var n) :=: (var (n ++ "_mem"))))

generateModelElementCondition p m (context (Previous (Properties n _ _ _ _ (s ∷ [])) (initValue ∷ [])) (e1 ∷ e2 ∷ [])) dag =
    (var (n ++ "_mem")) :=: (var (generateIdentifierAtEdge p m (e1 ∷ e2 ∷ []) 1 dag))

generateModelElementCondition p m (context (Textual (Properties n _ _ _ _ _) s) edges) dag =
    (var n) :=: const s

generateModelElementCondition _ _ _ _ = false

generateCondition : ∀ {n} -> Project -> Model -> ModelDAG n -> List ModelElement -> Condition
generateCondition p m ∅ seen = true
generateCondition p m ((context me edges) & dag) seen with containsModelElement seen me | me | edges | generateCondition p m dag seen | generateModelElementCondition p m (context me edges) dag
... | true | (Previous (Properties a b c d f ("" ∷ [])) _) | (e ∷ []) | true | c2 = c2
... | true | (Previous (Properties a b c d f ("" ∷ [])) _) | (e ∷ []) | c1 | c2 = c1 ∧ checkAndReplaceVarsInNewCondition c1 c2
... | true | (Previous (Properties a b c d f (s ∷ [])) _) | (e1 ∷ e2 ∷ []) | true | c2 = c2
... | true | (Previous (Properties a b c d f (s ∷ [])) _) | (e1 ∷ e2 ∷ []) | c1 | c2 = c1 ∧ checkAndReplaceVarsInNewCondition c1 c2
... | true | _ | _ | c1 | c2 = c1
... | false | _ | _ | true | c2 = c2
... | false | _ | _ | c1 | c2 = c1 ∧ checkAndReplaceVarsInNewCondition c1 c2

generateConditionDAGs : ∀ {n} -> Project -> Model -> List (ModelDAG n) -> List ModelElement -> Condition
generateConditionDAGs p m [] seen = true
generateConditionDAGs p m (dag ∷ dags) seen with generateCondition p m dag seen | generateConditionDAGs p m dags (seen Data.List.++ DAGToList dag)
... | true | true = true
... | true | c2 = c2
... | c1 | true = c1
... | c1 | c2 = c1 ∧ checkAndReplaceVarsInNewCondition c1 c2

generateModelDAGCondition : Project -> Model -> Maybe Condition
generateModelDAGCondition p (Operation n ins outs sms) with (createDAG (Operation n ins outs sms))
... | nothing = nothing
... | just dags = just (
    weaken
    (Defined (var "isInitialCycle") ∧ (generateConditionDAGs p (Operation n ins outs sms) dags []))
     ((var "isInitialCycle") ∷ (getModelElementVars (DAGsToListReverse dags)))
     ((var "isInitialCycle") ∷ (getModelElementVars (ins Data.List.++ outs)))
    )

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

checkGenerateAndVerify : Maybe Project -> String -> CodeGenerationResult
checkGenerateAndVerify (just p) n with findModelInProjectWithName p n
checkGenerateAndVerify (just p) n | just (Operation n2 ins outs sms) with checkModel (Operation n2 ins outs sms)
checkGenerateAndVerify (just p) n | just (Operation n2 ins outs sms) | [] with getInputsCondition ins | generateModelDAGCondition p (Operation n2 ins outs sms)
checkGenerateAndVerify (just p) n | just m                           | [] | preCondition | just postCondition with generateModelCodeCondition p m (Defined (var "isInitialCycle") ∧ preCondition)
checkGenerateAndVerify (just p) n | just m                           | [] | preCondition | just postCondition | just codePostCondition with postCondition ≟C codePostCondition
checkGenerateAndVerify (just p) n | just m                           | [] | preCondition | just postCondition | just codePostCondition | true = (generateCode p n) 
checkGenerateAndVerify (just p) n | just m                           | [] | preCondition | just postCondition | just codePostCondition | false = VerifyError
checkGenerateAndVerify (just p) n | just m                           | [] | preCondition | just postCondition | nothing = GenerationError ("Could not generate code post condition.")
checkGenerateAndVerify (just p) n | just m                           | [] | preCondition | nothing = GenerationError ("Could not generate model post condition.")
checkGenerateAndVerify (just p) n | just m                           | errors = CheckError errors
checkGenerateAndVerify (just p) n | nothing = GenerationError ("Could not find the root model " ++ n)
checkGenerateAndVerify nothing n = GenerationError ("There is no project.")

denemeGen : Model -> CodeGenerationResult
denemeGen m = generateModel (project "" [] [] [] []) m

denemeHoare : Model -> Maybe (List (HoareTriplet (List String)))
denemeHoare m = generateModelCodeHoareTriplets (project "" [] [] [] []) m

denemeCodeCond : Model -> Maybe Condition
denemeCodeCond (Operation n ins outs sms) = generateModelCodeCondition (project "" [] [] [] []) (Operation n ins outs sms)
    (Defined (var "isInitialCycle") ∧ (getInputsCondition ins))

denemeDAGCond : Model -> Maybe Condition
denemeDAGCond m = generateModelDAGCondition (project "" [] [] [] []) m

checkResult : Bool
checkResult with denemeCodeCond doubleOutputModel | denemeDAGCond doubleOutputModel
... | just c1 | just c2 = c1 ≟C c2
... | _ | _ = false

checkResult2 : Bool
checkResult2 with denemeCodeCond ifExample | denemeDAGCond ifExample
... | just c1 | just c2 = c1 ≟C c2
... | _ | _ = false

checkResult3 : Bool
checkResult3 with denemeCodeCond ifExample2 | denemeDAGCond ifExample2
... | just c1 | just c2 = c1 ≟C c2
... | _ | _ = false

checkResult4 : Bool
checkResult4 with denemeCodeCond ifExample3 | denemeDAGCond ifExample3
... | just c1 | just c2 = c1 ≟C c2
... | _ | _ = false

checkResult5 : Bool
checkResult5 with denemeCodeCond previousExample | denemeDAGCond previousExample
... | just c1 | just c2 = c1 ≟C c2
... | _ | _ = false

checkResult6 : Bool
checkResult6 with denemeCodeCond previousCycle | denemeDAGCond previousCycle
... | just c1 | just c2 = c1 ≟C c2
... | _ | _ = false

checkResult7 : Bool
checkResult7 with denemeCodeCond previousCycle2 | denemeDAGCond previousCycle2
... | just c1 | just c2 = c1 ≟C c2
... | _ | _ = false

testHoare : checkResult ≡ true
testHoare = refl

testHoare2 : checkResult2 ≡ true
testHoare2 = refl

testHoare3 : checkResult3 ≡ true
testHoare3 = refl

testHoare4 : checkResult4 ≡ true
testHoare4 = refl

testHoare5 : checkResult5 ≡ true
testHoare5 = refl

testHoare6 : checkResult6 ≡ true
testHoare6 = refl

testHoare7 : checkResult7 ≡ true
testHoare7 = refl

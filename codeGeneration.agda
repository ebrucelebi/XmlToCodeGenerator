{-# OPTIONS --safe #-}

module codeGeneration where

open import utility
open import IMODEDataTypes
open import ModelDAG
open import createDAG
open import checkProject

open import Data.String
open import Data.Maybe
open import Data.Bool
open import Data.Product
open import Data.List hiding (concat; _++_)
open import Data.Fin hiding (join)
open import Data.Nat
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

mutual
    generateEdges : ∀ {n} -> Project -> List ModelElement -> CodeSection -> List (ModelElement × Fin n) -> ModelDAG n -> (List String) × (List ModelElement)
    generateEdges _ seen _ [] _ = ([] , seen)
    generateEdges p seen _ (e ∷ xs) ∅ = ([] , seen)
    generateEdges p seen section (e ∷ xs) (c & dag) with generateEdges p seen section xs (c & dag)
    generateEdges p seen section (e ∷ xs) (c & dag) | (res1 , seen1) with e
    generateEdges p seen section (e ∷ xs) (c & dag) | (res1 , seen1) | (_ , zero) with generateModelElement p seen1 section c dag
    generateEdges p seen section (e ∷ xs) (c & dag) | (res1 , seen1) | (_ , zero) | (res2 , seen2) = (concatenateTwoList res1 res2 , seen2)
    generateEdges p seen section (e ∷ xs) (c & dag) | (res1 , seen1) | (me , (suc m)) with generateEdges p seen1 section ((me , m) ∷ []) dag
    generateEdges p seen section (e ∷ xs) (c & dag) | (res1 , seen1) | (me , (suc m)) | (res2 , seen2) = (concatenateTwoList res1 res2 , seen2)

    generateIdentifierEdge : ∀ {n} -> Project -> ModelElement × Fin n -> ModelDAG n -> String
    generateIdentifierEdge p e dag with generateEdges p [] Identifier (e ∷ []) dag
    ... | (x ∷ [] , _) = x
    ... | _ = ""

    generateIdentifierAtEdge : ∀ {n} -> Project -> List (ModelElement × Fin n) -> ℕ -> ModelDAG n -> String
    generateIdentifierAtEdge p [] n dag = ""
    generateIdentifierAtEdge p (e ∷ es) zero dag = generateIdentifierEdge p e dag
    generateIdentifierAtEdge p (e ∷ es) (suc n) dag = generateIdentifierAtEdge p es n dag
    
    generateIdentifierEdges : ∀ {n} -> Project -> List (ModelElement × Fin n) -> ModelDAG n -> List String
    generateIdentifierEdges _ [] _ = []
    generateIdentifierEdges p (e ∷ es) dag = (generateIdentifierEdge p e dag) ∷ (generateIdentifierEdges p es dag)

    generateIdentifierContext : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> String
    generateIdentifierContext p c dag with generateModelElement p [] Identifier c dag
    ... | (x ∷ [] , _) = x
    ... | _ = ""

    generateOutputMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateOutputMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ ";") ∷ []

    generateAdditionMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateAdditionMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (join (generateIdentifierEdges p edges dag) " + ") ++ ";") ∷ []

    generateMultiplicationMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateMultiplicationMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (join (generateIdentifierEdges p edges dag) " * ") ++ ";") ∷ []

    -- TODO: Add cast type
    generateNumericCastMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateNumericCastMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ ";") ∷ []

    generatePolymorphicDivisionMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generatePolymorphicDivisionMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " / " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []

    generateSubtractionMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateSubtractionMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " - " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []
                                  
    generateUnaryMinusMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateUnaryMinusMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = -" ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ ";") ∷ []

    generateLogicalAndMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateLogicalAndMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (join (generateIdentifierEdges p edges dag) " && ") ++ ";") ∷ []

    generateLogicalNorMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateLogicalNorMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = !(" ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " || " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ");") ∷ []
                                  
    generateLogicalNotMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateLogicalNotMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = !" ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ ";") ∷ []

    generateLogicalOrMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateLogicalOrMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (join (generateIdentifierEdges p edges dag) " || ") ++ ";") ∷ []

    generateLogicalSharpMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateLogicalSharpMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (join (generateIdentifierEdges p edges dag) " + ") ++ " <= 1;") ∷ []

    generateLogicalXorMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateLogicalXorMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " ^ " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []

    generateBitwiseAndMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateBitwiseAndMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " & " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []

    generateBitwiseNotMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateBitwiseNotMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = ~" ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ ";") ∷ []

    generateBitwiseOrMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateBitwiseOrMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " | " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []

    generateBitwiseXorMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateBitwiseXorMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " ^ " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []

    generateLeftShiftMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateLeftShiftMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " << " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []

    generateRightShiftMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateRightShiftMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " >> " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []

    -- TODO: After creating types header with compare functions, fix different code.
    generateDifferentMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateDifferentMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " != " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []

    -- TODO: After creating types header with compare functions, fix equal code.
    generateEqualMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateEqualMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " == " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []

    generateGreaterThanEqualMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateGreaterThanEqualMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " >= " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []
                                  
    generateLessThanEqualMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateLessThanEqualMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " <= " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []
                                  
    generateStrictlyGreaterThanMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateStrictlyGreaterThanMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " > " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []
                                  
    generateStrictlyLessThanMain : ∀ {n} -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateStrictlyLessThanMain p (context me edges) dag = ((generateIdentifierContext p (context me edges) dag) ++ " = " ++
                                  (generateIdentifierAtEdge p edges 0 dag) ++ " < " ++ (generateIdentifierAtEdge p edges 1 dag) ++ ";") ∷ []
                                  
    generateModelElementMain : ∀ {n} -> ModelElement -> Project -> Context ModelElement ModelElement n -> ModelDAG n -> List String
    generateModelElementMain (OutputInstance _ _) p c dag = generateOutputMain p c dag
    generateModelElementMain (Addition _) p c dag = generateAdditionMain p c dag
    generateModelElementMain (Multiplication _) p c dag = generateMultiplicationMain p c dag
    generateModelElementMain (InputInstance _ _) p c dag = []
    generateModelElementMain (NumericCast _) p c dag = generateNumericCastMain p c dag
    generateModelElementMain (PolymorphicDivision _) p c dag = generatePolymorphicDivisionMain p c dag
    generateModelElementMain (Subtraction _) p c dag = generateSubtractionMain p c dag
    generateModelElementMain (UnaryMinus _) p c dag = generateUnaryMinusMain p c dag
    generateModelElementMain (LogicalAnd _) p c dag = generateLogicalAndMain p c dag
    generateModelElementMain (LogicalNor _) p c dag = generateLogicalNorMain p c dag
    generateModelElementMain (LogicalNot _) p c dag = generateLogicalNotMain p c dag
    generateModelElementMain (LogicalOr _) p c dag = generateLogicalOrMain p c dag
    generateModelElementMain (LogicalSharp _) p c dag = generateLogicalSharpMain p c dag
    generateModelElementMain (LogicalXor _) p c dag = generateLogicalXorMain p c dag
    generateModelElementMain (BitwiseAnd _) p c dag = generateBitwiseAndMain p c dag
    generateModelElementMain (BitwiseNot _) p c dag = generateBitwiseNotMain p c dag
    generateModelElementMain (BitwiseOr _) p c dag = generateBitwiseOrMain p c dag
    generateModelElementMain (BitwiseXor _) p c dag = generateBitwiseXorMain p c dag
    generateModelElementMain (LeftShift _) p c dag = generateLeftShiftMain p c dag
    generateModelElementMain (RightShift _) p c dag = generateRightShiftMain p c dag
    generateModelElementMain (Different _) p c dag = generateDifferentMain p c dag
    generateModelElementMain (Equal _) p c dag = generateEqualMain p c dag
    generateModelElementMain (GreaterThanEqual _) p c dag = generateGreaterThanEqualMain p c dag
    generateModelElementMain (LessThanEqual _) p c dag = generateLessThanEqualMain p c dag
    generateModelElementMain (StrictlyGreaterThan _) p c dag = generateStrictlyGreaterThanMain p c dag
    generateModelElementMain (StrictlyLessThan _) p c dag = generateStrictlyLessThanMain p c dag
    generateModelElementMain _ p c dag = []

    generateModelElement : ∀ {n} -> Project -> List ModelElement -> CodeSection -> Context ModelElement ModelElement n -> ModelDAG n -> (List String) × (List ModelElement)
    generateModelElement p seen Identifier (context me edges) dag = ((getModelElementName me) ∷ [] , seen)
    generateModelElement p seen Main (context me edges) dag with containsModelElement seen me
    ... | true = ([] , seen)
    ... | false with generateEdges p seen Main edges dag
    ... | (res , seen1) = (generateModelElementMain me p (context me edges) dag Data.List.++ res , me ∷ seen1)

-- Go over DAG and call generate Main code for the model element. Skip it if it is already generated (added to the seen).
-- Later model elements might be generated before this function arrives to that model element because of the edges.
generateModelElements : ∀ {n} -> Project -> List ModelElement -> CodeSection -> ModelDAG n -> (List String) × (List ModelElement)
generateModelElements _ seen section ∅ = ([] , seen)
generateModelElements p seen section ((context me edges) & dag) with containsModelElement seen me
generateModelElements p seen section (c & dag) | true = generateModelElements p seen section dag
generateModelElements p seen section (c & dag) | false with generateModelElement p seen section c dag
...                                         | (res1 , seen1) with generateModelElements p seen1 section dag
...                                         | (res2 , seen2) = (concatenateTwoList (Data.List.reverse res1) res2 , seen2)

generateModelSource : ∀ {n} -> Project -> String -> ModelDAG n -> GeneratedFile
generateModelSource p n dag with generateModelElements p [] Main dag
... | (mainContent , _) = File (n ++ ".c") (encapsulateBraces mainContent)

-- Create DAG and start the code generation for the model elements in the order.
generateModel : Project -> Model -> CodeGenerationResult
generateModel p (Operation n ins outs sms) with (createDAG (Operation n ins outs sms))
... | nothing = GenerationError ("Could not generate DAG for" ++ n)
... | just dag = Success (generateModelSource p n dag ∷ [])

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

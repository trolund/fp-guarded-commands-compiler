// Michael R. Hansen 07-06-2021


// You must revise the following path 

#r @"packages/FsLexYacc.Runtime.7.0.6/lib/portable-net45+netcore45+wpa81+wp8+MonoAndroid10+MonoTouch10/FsLexYacc.Runtime.dll";

#load "AST.fs"
#load "Parser.fs"
#load "Lexer.fs"
#load "TypeCheck.fs"
#load "Machine.fs"
#load "CodeGen.fs"
#load "CodeGenOpt.fs"
#load "VirtualMachine.fs"
#load "Util.fs"
#load "./TreeManager/Library.fs"
#load "./PostScriptGenerator/Library.fs"


open GuardedCommands.Util
open GuardedCommands.Frontend.TypeCheck
open GuardedCommands.Frontend.AST
open GuardedCommands.Backend.CodeGeneration
// open GuardedCommands.Backend.CodeGenerationOpt
open PostScriptGenerator.Generator
open Tree.TreeManager

open ParserUtil
open CompilerUtil



System.IO.Directory.SetCurrentDirectory __SOURCE_DIRECTORY__;;

// Basic tests ///////////////////////////////

let testFile = "test_extensions/tc_cond_2.gc";;

let testTree = parseFromFile testFile

let _ = tcP testTree;;

let testAndCode = CP testTree;; 

let _ = go testTree;;

let _ = goOptTrace testTree;;
let _ = goTrace testTree;;

let _ = execOpt testFile
let _ = exec testFile

// tree print

let programToPS (fn: string) =
    let words = fn.Split [|'/'|]
    parseFromFile fn |> parseProgram |> treeToFile (words.[words.Length - 1])

programToPS "test_6/tc_overwritingAss.gc"

// The Ex0.gc example:

let ex0Tree = parseFromFile "test/Ex0.gc";;

let _ = tcP ex0Tree;;

let ex0Code = CP ex0Tree;; 

let _ = go ex0Tree;;

let _ = goTrace ex0Tree;;


// Parsing of Ex1.gc

let ex1Tree = parseFromFile "test/Ex1.gc";; 

// -- is typechecked as follows:

let _ = tcP ex1Tree;;

// obtain symbolic code:
let ex1Code = CP ex1Tree;; 

// -- is executed with trace as follows:
let stack = goTrace ex1Tree;;

// -- is executed as follows (no trace):
let sameStack = go ex1Tree;;

// "All in one" parse from file, type check, compile and run 

let _ = exec "test/Ex1.gc";;

let _ = exec "test/Ex2.gc";;

// Test of programs covered by the fifth task using optimized compilation (Section 8.2):
List.iter execOpt ["test/Ex1.gc"; "test/Ex2.gc"];;

// All programs relating to the basic version can be parsed:
let pts = List.map parseFromFile ["test/Ex1.gc"; "test/Ex2.gc";"test/Ex3.gc"; "test/Ex4.gc"; "test/Ex5.gc"; "test/Ex6.gc"; "test/Skip.gc"];;

// The parse tree for Ex3.gc
List.item 2 pts ;;

let ex3Tree = parseFromFile "test/Ex3.gc";;

let _ = tcP ex3Tree;;

let ex3Code = CP ex3Tree;; 

let _ = go ex3Tree;;

let _ = goTrace ex3Tree;;

let _ = exec "test/Ex3.gc";;


// Test of programs covered by the first task (Section 3.7):
List.iter exec ["test/Ex1.gc"; "test/Ex2.gc";"test/Ex3.gc"; "test/Ex4.gc"; "test/Ex5.gc"; "test/Ex6.gc"; "test/Skip.gc"];;

// Test of programs covered by the second task (Section 4.3):
List.iter exec ["test/Ex7.gc"; "test/fact.gc"; "test/factRec.gc"; "test/factCBV.gc"];;

// Test of programs covered by the fourth task (Section 5.4):
List.iter exec ["test/A0.gc"; "test/A1.gc"; "test/A2.gc"; "test/A3.gc"];;

// Test of programs covered by the fifth task (Section 6.1):
List.iter exec ["test/A4.gc"; "test/Swap.gc"; "test/QuickSortV1.gc"];;

// Test of programs covered by the fifth task (Section 7.4):
List.iter exec ["test/par1.gc"; "test/factImpPTyp.gc"; "test/QuickSortV2.gc"];;

// Test of programs covered by the fifth task using optimized compilation (Section 8.2):
List.iter execOpt ["test/par1.gc"; "test/factImpPTyp.gc"; "test/QuickSortV2.gc"];;

// OWN TESTS

// Test of programs covered test_3
List.iter exec ["test_3/tc_alternative_2.gc"; "test_3/tc_alternative_1.gc"; "test_3/tc_alternative_stop.gc"; "test_3/tc_alternative.gc"; "test_3/tc_and.gc"; "test_3/tc_division.gc"; "test_3/tc_equal.gc"; "test_3/tc_greaterthan.gc"; "test_3/tc_greaterthanequals.gc"; "test_3/tc_lessthan.gc"; "test_3/tc_minus.gc"; "test_3/tc_modulus.gc"; "test_3/tc_negation_2.gc"; "test_3/tc_negation.gc"; "test_3/tc_notequal.gc"; "test_3/tc_or.gc"; "test_3/tc_plus.gc"; "test_3/tc_repetition.gc"; "test_3/tc_times.gc"];;
List.iter execOpt ["test_3/tc_alternative_2.gc"; "test_3/tc_alternative_1.gc"; "test_3/tc_alternative_stop.gc"; "test_3/tc_alternative.gc"; "test_3/tc_and.gc"; "test_3/tc_division.gc"; "test_3/tc_equal.gc"; "test_3/tc_greaterthan.gc"; "test_3/tc_greaterthanequals.gc"; "test_3/tc_lessthan.gc"; "test_3/tc_minus.gc"; "test_3/tc_modulus.gc"; "test_3/tc_negation_2.gc"; "test_3/tc_negation.gc"; "test_3/tc_notequal.gc"; "test_3/tc_or.gc"; "test_3/tc_plus.gc"; "test_3/tc_repetition.gc"; "test_3/tc_times.gc"];;

// Test of programs covered test_4
List.iter exec ["test_4/tc_func_app_1.gc"; "test_4/tc_func_app_2.gc"; "test_4/tc_func_app_3.gc"; "test_4/tc_func_app_4.gc"; "test_4/tc_func_app_5.gc"; "test_4/tc_func_app_6.gc"; "test_4/tc_func_app.gc"; "test_4/tc_func_dec_1.gc"; "test_4/tc_func_dec_2.gc"; "test_4/tc_func_dec_3.gc"; "test_4/tc_func_dec_4.gc"; "test_4/tc_func_dec_alternative.gc"; "test_4/tc_func_global_dec_ass_1.gc"; "test_4/tc_func_local_dec_1.gc"; "test_4/tc_func_local_dec_2.gc"; "test_4/tc_func_local_dec_3.gc"; "test_4/tc_func_local_dec_app_1.gc"; "test_4/tc_func_local_dec_app_2.gc"; "test_4/tc_func_local_dec_app_3.gc"; "test_4/tc_local_dec_non_func_correct.gc"; "test_4/tc_local_dec.gc"];;
List.iter execOpt ["test_4/tc_func_app_1.gc"; "test_4/tc_func_app_2.gc"; "test_4/tc_func_app_3.gc"; "test_4/tc_func_app_4.gc"; "test_4/tc_func_app_5.gc"; "test_4/tc_func_app_6.gc"; "test_4/tc_func_app.gc"; "test_4/tc_func_dec_1.gc"; "test_4/tc_func_dec_2.gc"; "test_4/tc_func_dec_3.gc"; "test_4/tc_func_dec_4.gc"; "test_4/tc_func_dec_alternative.gc"; "test_4/tc_func_global_dec_ass_1.gc"; "test_4/tc_func_local_dec_1.gc"; "test_4/tc_func_local_dec_2.gc"; "test_4/tc_func_local_dec_3.gc"; "test_4/tc_func_local_dec_app_1.gc"; "test_4/tc_func_local_dec_app_2.gc"; "test_4/tc_func_local_dec_app_3.gc"; "test_4/tc_local_dec_non_func_correct.gc"; "test_4/tc_local_dec.gc"];;

// Test of programs covered test_5
List.iter exec ["test_5/tc_array_dec.gc"; "test_5/tc_array_index_ass_op.gc"; "test_5/tc_array_index_ass.gc"; "test_5/tc_array_index.gc"; "test_5/tc_func_taking_array.gc"];;
List.iter execOpt ["test_5/tc_array_dec.gc"; "test_5/tc_array_index_ass_op.gc"; "test_5/tc_array_index_ass.gc"; "test_5/tc_array_index.gc"; "test_5/tc_func_taking_array.gc"];;
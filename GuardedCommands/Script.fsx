﻿// Michael R. Hansen 07-06-2021


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
open PostScriptGenerator.Generator
open Tree.TreeManager

open ParserUtil
open CompilerUtil



System.IO.Directory.SetCurrentDirectory __SOURCE_DIRECTORY__;;

// Basic tets ///////////////////////////////

let testAndTree = parseFromFile "test/A0.gc";;

let _ = tcP testAndTree;;

let testAndCode = CP testAndTree;; 

let _ = go testAndTree;;

let _ = goTrace testAndTree;;

let _ = exec "test_4/test_func_local_dec_app_1.gc";;

// tree print

let programToPS (fn: string) =
    let words = fn.Split [|'/'|]
    parseFromFile fn |> parseProgram |> treeToFile (words.[words.Length - 1])

programToPS "test_6/tc_simpleCase.gc"

// The Ex0.gc example:

let ex0Tree = parseFromFile "Ex0.gc";;

let _ = tcP ex0Tree;;

let ex0Code = CP ex0Tree;; 

let _ = go ex0Tree;;

let _ = goTrace ex0Tree;;


// Parsing of Ex1.gc

let ex1Tree = parseFromFile "Ex1.gc";; 

// -- is typechecked as follows:

let _ = tcP ex1Tree;;

// obtain symbolic code:
let ex1Code = CP ex1Tree;; 

// -- is executed with trace as follows:
let stack = goTrace ex1Tree;;

// -- is executed as follows (no trace):
let sameStack = go ex1Tree;;

// "All in one" parse from file, type check, compile and run 

let _ = exec "Ex1.gc";;

let _ = exec "Ex2.gc";;

// Test of programs covered by the fifth task using optimized compilation (Section 8.2):
List.iter execOpt ["Ex1.gc"; "Ex2.gc"];;

// All programs relating to the basic version can be parsed:
let pts = List.map parseFromFile ["Ex1.gc"; "Ex2.gc";"Ex3.gc"; "Ex4.gc"; "Ex5.gc"; "Ex6.gc"; "Skip.gc"];;

// The parse tree for Ex3.gc
List.item 2 pts ;;




let ex3Tree = parseFromFile "Ex3.gc";;

let _ = tcP ex3Tree;;

let ex3Code = CP ex3Tree;; 

let _ = go ex3Tree;;

let _ = goTrace ex3Tree;;

let _ = exec "Ex3.gc";;

(*
// Test of programs covered by the first task (Section 3.7):
List.iter exec ["Ex1.gc"; "Ex2.gc";"Ex3.gc"; "Ex4.gc"; "Ex5.gc"; "Ex6.gc"; "Skip.gc"];;

// Test of programs covered by the second task (Section 4.3):
List.iter exec ["Ex7.gc"; "fact.gc"; "factRec.gc"; "factCBV.gc"];;

// Test of programs covered by the fourth task (Section 5.4):
List.iter exec ["A0.gc"; "A1.gc"; "A2.gc"; "A3.gc"];;

// Test of programs covered by the fifth task (Section 6.1):
List.iter exec ["A4.gc"; "Swap.gc"; "QuickSortV1.gc"];;

// Test of programs covered by the fifth task (Section 7.4):
List.iter exec ["par1.gc"; "factImpPTyp.gc"; "QuickSortV2.gc"; "par2.gc"];;

// Test of programs covered by the fifth task using optimized compilation (Section 8.2):
List.iter execOpt ["par1.gc"; "factImpPTyp.gc"; "QuickSortV2.gc"; "par2.gc"];;

*)

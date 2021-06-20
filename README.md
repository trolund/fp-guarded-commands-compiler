# FP-Project 2 - A compiler for Guarded Commands

This project is made by Group 12 in the course 02257 Applied Functional Programming at DTU.

### Group 12 consist of:
* Daniel Larsen, s151641
* Emil Toftegaard Gæde, s164414
* Niklas Broch Thielemann, s145032
* Troels Lund, s161791

### Abstract

### Project structure

* PostScriptGenerator
   - Contains all code to produce the Postscript tree drawings.
   
* TreeManager
    - Contains all functions to manipulate trees.

* GuardedCommands
    - Contain the compiler. 

## Run the project

### Before running 

before running the project it needed to run __prebuild.sh__ on MacOS and Linux or __prebuild.bat__ on Windows

### Run 

To run the compiler use the __Script.fsx__ with F# interactive environment.

A large number of test programs can be found in the _input_ folder. 

AST trees can be generated as PostScript and will be saved in the _output_ folder. 


namespace GuardedCommands.Backend
// Michael R. Hansen 05-01-2016, 04-01-2018, 07-07-2021
// This file is obtained by an adaption of the file MicroC/Comp.fs by Peter Sestoft

open Machine
open GuardedCommands.Frontend.AST

module CodeGeneration =

    (* A global variable has an absolute address, a local one has an offset: *)
    type Var = 
        | GloVar of int (* absolute address in stack           *)
        | LocVar of int (* address relative to bottom of frame *)

    (* The variable environment keeps track of global and local variables, and 
       keeps track of next available offset for local variables *)
    type varEnv = Map<string, Var * Typ> * int
    
    (* The function environment maps function name to label and parameter decs *)
    type ParamDecs = (Typ * string) list
    type funEnv = Map<string, label * Typ option * ParamDecs>

    (* Bind declared parameters in env: *)
    let addLocVar vEnv (t, s) = let (vEnv', fdepth) = vEnv
                                ((Map.add s (LocVar fdepth, t) vEnv'), fdepth + 1)

    let addLocVars vEnv p = 
        List.fold addLocVar vEnv p

    let lookupFun fEnv s  = 
                match Map.tryFind s fEnv with 
                | None    -> failwith ("lookup: " + s + " not found.")
                | Some(x) -> x 
                
    let lookupVar vEnv s =
                let (vEnv', _) = vEnv
                match Map.tryFind s vEnv' with 
                | None    -> failwith ("lookup: " + s + " not found.")
                | Some(x) -> x             

    (* Bind declared variable in env and generate code to allocate it: *)   
    let allocate (kind : int -> Var) (typ, x) vEnv =
        let (env, fdepth) = vEnv 
        match typ with
        | ATyp (ATyp _, _) -> raise (Failure "allocate: array of arrays not permitted")
        | ATyp (_, Some i) -> let newEnv = (Map.add x (kind (fdepth + i), typ) env, fdepth + i + 1)
                              (newEnv, [INCSP i; GETSP; CSTI (i - 1); SUB])
        | _                -> let newEnv = (Map.add x (kind fdepth, typ) env, fdepth + 1)
                              (newEnv, [INCSP 1])

    let rec repeat n s acc =
        match n with 
        | 0 -> acc
        | _ -> repeat (n-1) s (acc @ s) 

    /// CE vEnv fEnv e gives the code for an expression e on the basis of a variable and a function environment
    let rec CE (vEnv : varEnv) fEnv = function
        | N n                   -> [CSTI n]
        | B b                   -> [CSTI (if b then 1 else 0)]
        | Access acc            -> CA vEnv fEnv acc @ [LDI] 
        | Addr acc              -> CA vEnv fEnv acc // muligvis ikke rigtig.
        | Apply("-", [e])       -> CE vEnv fEnv e @ [CSTI 0; SWAP; SUB]
        | Apply("!", [b])       -> CE vEnv fEnv b @ [NOT] // muligvis ikke rigtig.
        | Apply(o, [b1; b2]) when List.exists (fun x -> o = x) ["&&"; "||"; "<>"]
                                -> match o with
                                   | "&&" -> let labend   = newLabel()
                                             let labfalse = newLabel()
                                             CE vEnv fEnv b1 @ [IFZERO labfalse] @ CE vEnv fEnv b2 @
                                             [GOTO labend; Label labfalse; CSTI 0; Label labend]
                                   | "<>" -> CE vEnv fEnv b1 @ CE vEnv fEnv b2 @ [EQ; NOT]
                                   | "||" -> let labend   = newLabel()
                                             let labtrue = newLabel()
                                             CE vEnv fEnv b1 @ [IFNZRO labtrue] @ CE vEnv fEnv b2 @
                                             [GOTO labend; Label labtrue; CSTI 1; Label labend]
                                   | _    -> failwith "CE: this case is not possible"
        | Apply(o, [e1; e2]) when List.exists (fun x -> o = x) ["+"; "-"; "*"; "/"; "%"; "="; "<"; ">"; "<="; ">="]
                                -> let ins = match o with
                                             | "+"  -> [ADD]
                                             | "-"  -> [SUB]
                                             | "*"  -> [MUL]
                                             | "/"  -> [DIV]
                                             | "%"  -> [MOD]
                                             | "="  -> [EQ]
                                             | "<"  -> [LT]
                                             | ">"  -> [SWAP; LT]
                                             | "<=" -> [SWAP; LT; NOT]
                                             | ">=" -> [LT; NOT]
                                             | _    -> failwith "CE: this case is not possible"
                                   CE vEnv fEnv e1 @ CE vEnv fEnv e2 @ ins
        | Apply(f, es) -> call vEnv fEnv f es
        | _            -> failwith "CE: not supported yet"
    and CEs vEnv fEnv es = 
        List.collect (CE vEnv fEnv) es
     
    and call vEnv fEnv f es = let (label, _, p) = lookupFun fEnv f
                              let pLen = List.length p
                              CEs vEnv fEnv es @
                              [CALL (pLen, label)]

    /// CA vEnv fEnv acc gives the code for an access acc on the basis of a variable and a function environment
    and CA vEnv fEnv = function 
        | AVar x          -> match lookupVar vEnv x with
                             | (GloVar addr, _) -> [CSTI addr]
                             | (LocVar addr, _) -> [GETBP; CSTI addr; ADD]
        | AIndex(acc, e)  -> CA vEnv fEnv acc @ [LDI] @ CE vEnv fEnv e @ [ADD]
        | ADeref e        -> CE vEnv fEnv e // failwith "CA: pointer dereferencing not supported yet"
    and CAs vEnv fEnv accs = List.collect (CA vEnv fEnv) accs
    /// CS vEnv fEnv s gives the code for a statement s on the basis of a variable and a function environment                          
    let rec CS vEnv fEnv = function
        | PrintLn e         -> CE vEnv fEnv e @ [PRINTI; INCSP -1] 
        | Ass(acc, e)       -> let n = e.Length
                               CEs vEnv fEnv e @ CAs vEnv fEnv acc @ repeat n [GETSP; CSTI n; SUB; LDI; STI; INCSP -1] [] @ repeat n [INCSP -1] []
        | Return(o)         -> match o with   
                               | Some(v) -> CE vEnv fEnv v @ [RET (snd vEnv)]
                               | None    -> [RET (snd vEnv - 1)]
        | Alt (gc)          -> let endLabel = newLabel()
                               alt' vEnv fEnv endLabel gc @ 
                               [STOP] @ [Label endLabel]
        | Do (gc)           -> let startLabel = newLabel()
                               [Label startLabel] @
                               do' vEnv fEnv startLabel gc                       
        | Block([], stms)   -> CSs vEnv fEnv stms
        | Block(decs, stms) -> let (vEnv', code) = compileLocalDecs (vEnv, []) decs
                               code @ CSs vEnv' fEnv stms @
                               [INCSP -(List.length decs - 1)]
        | Call (f, es)      -> call vEnv fEnv f es
                               @ [INCSP -1]
    and CSs vEnv fEnv stms = List.collect (CS vEnv fEnv) stms 

    and alt' vEnv fEnv el = function
        | GC ([])              -> []
        | GC ((b, stms)::alts) -> let labnext = newLabel()
                                  CE vEnv fEnv b @
                                  [IFZERO labnext] @ 
                                  CSs vEnv fEnv stms @
                                  [GOTO el] @
                                  [Label labnext] @
                                  alt' vEnv fEnv el (GC (alts))
    and do' vEnv fEnv sl = function
        | GC ([])              -> []
        | GC ((b, stms)::alts) -> let labnext = newLabel()
                                  CE vEnv fEnv b @
                                  [IFZERO labnext] @ 
                                  CSs vEnv fEnv stms @
                                  [GOTO sl] @
                                  [Label labnext] @
                                  do' vEnv fEnv sl (GC (alts))

    and compileLocalDec vEnv = function
         | VarDec (t, s) -> let (vEnv', code') = allocate LocVar (t, s) vEnv
                            (vEnv', code')
         | FunDec _      -> (vEnv, [])
    and compileLocalDecs (vEnv, code) = function
         | []    -> (vEnv, code)
         | d::ds -> let (vEnv', code') = compileLocalDec vEnv d
                    compileLocalDecs (vEnv', code @ code') ds
    
    let rec compileFunc vEnv fEnv = function
         | VarDec _              -> []
         | FunDec (_, s, _, stm) -> let vEnv' = (fst vEnv, 0)
                                    let (label, _, p) = lookupFun fEnv s
                                    let localvEnv = addLocVars vEnv' p
                                    [Label label] @
                                    CS localvEnv fEnv stm @
                                    [RET (List.length p - 1)]
    and compileFuncs vEnv fEnv decs = 
        List.collect (compileFunc vEnv fEnv) decs

    (* ------------------------------------------------------------------- *)
    
    (* Build environments for global variables and functions *)
    let makeGlobalEnvs decs = 
        let decv = function
            | VarDec (t, s) -> (t, s)
            | FunDec _      -> failwith ("decv: A function parameter can not be a function itself")

        let rec addv decs vEnv (fEnv : funEnv) = 
            match decs with
            | []         -> (vEnv, fEnv, [])
            | dec::decr  -> match dec with
                            | VarDec (typ, var)        -> let (vEnv1, code1) = allocate GloVar (typ, var) vEnv
                                                          let (vEnv2, fEnv2, code2) = addv decr vEnv1 fEnv
                                                          (vEnv2, fEnv2, code1 @ code2)
                            | FunDec (tyOpt, f, xs, _) -> addv decr vEnv (Map.add f ((newLabel(), tyOpt, List.map decv xs)) fEnv)
        addv decs (Map.empty, 0) Map.empty


    /// CP prog gives the code for a program prog
    let CP (P(decs, stms)) = 
       let _ = resetLabels ()
       let ((gvM, _) as gvEnv, fEnv, initCode) = makeGlobalEnvs decs
       initCode @ CSs gvEnv fEnv stms @ [STOP] @ compileFuncs gvEnv fEnv decs
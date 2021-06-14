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

    (* Bind declared variable in env and generate code to allocate it: *)   
    let allocate (kind : int -> Var) (typ, x) (vEnv : varEnv) =
        let (env, fdepth) = vEnv 
        match typ with
        | ATyp (ATyp _, _) -> raise (Failure "allocate: array of arrays not permitted")
        | ATyp (t, Some i) -> failwith "allocate: array not supported yet"
        | _                -> let newEnv = (Map.add x (kind fdepth, typ) env, fdepth + 1)
                              let code = [INCSP 1]
                              (newEnv, code)

    /// CE vEnv fEnv e gives the code for an expression e on the basis of a variable and a function environment
    let rec CE vEnv fEnv = function
        | N n                   -> [CSTI n]
        | B b                   -> [CSTI (if b then 1 else 0)]
        | Access acc            -> CA vEnv fEnv acc @ [LDI] 
        | Addr acc              -> CA vEnv fEnv acc @ [LDI] // muligvis ikke rigtig.
        | Apply("-", [e])       -> CE vEnv fEnv e @ [CSTI 0; SWAP; SUB]
        | Apply("!", [b])       -> CE vEnv fEnv b @ [NOT] // muligvis ikke rigtig.
        | Apply(o, [b1; b2]) when List.exists (fun x -> o = x) ["&&"; "||"; "<>"]
                                -> match o with
                                   | "&&" -> let labend   = newLabel()
                                             let labfalse = newLabel()
                                             CE vEnv fEnv b1 @ [IFZERO labfalse] @ CE vEnv fEnv b2
                                             @ [GOTO labend; Label labfalse; CSTI 0; Label labend]
                                   | "<>" -> CE vEnv fEnv b1 @ CE vEnv fEnv b2 @ [EQ; NOT]
                                   | "||" -> let labend   = newLabel()
                                             let labtrue = newLabel()
                                             CE vEnv fEnv b1 @ [IFNZRO labtrue] @ CE vEnv fEnv b2
                                             @ [GOTO labend; Label labtrue; CSTI 1; Label labend]
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
                                             | ">"  -> [SWAP; SUB; CSTI 0; LT]
                                             | "<=" -> let labend = newLabel()
                                                       let labtrue = newLabel()
                                                       [LT] @ [IFNZRO labtrue] @
                                                       CE vEnv fEnv e1 @ CE vEnv fEnv e2 @ [EQ] @ [IFNZRO labtrue] @
                                                       [CSTI 0] @ [GOTO labend] @ [Label labtrue] @ [CSTI 1] @ [Label labend]
                                             | ">=" -> let labend = newLabel()
                                                       let labtrue = newLabel()
                                                       [SWAP; DIV; CSTI 0; EQ] @ [IFNZRO labtrue] @
                                                       CE vEnv fEnv e1 @ CE vEnv fEnv e2 @ [EQ] @ [IFNZRO labtrue] @
                                                       [CSTI 0] @ [GOTO labend] @ [Label labtrue] @ [CSTI 1] @ [Label labend]
                                             | _    -> failwith "CE: this case is not possible"
                                   CE vEnv fEnv e1 @ CE vEnv fEnv e2 @ ins
        | _            -> failwith "CE: not supported yet"
    /// CA vEnv fEnv acc gives the code for an access acc on the basis of a variable and a function environment
    and CA vEnv fEnv = function 
        | AVar x          -> match Map.find x (fst vEnv) with
                             | (GloVar addr, _) -> [CSTI addr]
                             | (LocVar addr, _) -> failwith "CA: Local variables not supported yet"
        | AIndex(acc, e)  -> failwith "CA: array indexing not supported yet" 
        | ADeref e        -> failwith "CA: pointer dereferencing not supported yet"

    /// CS vEnv fEnv s gives the code for a statement s on the basis of a variable and a function environment                          
    let rec CS vEnv fEnv = function
        | PrintLn e       -> CE vEnv fEnv e @ [PRINTI; INCSP -1] 
        | Ass(acc, e)     -> CA vEnv fEnv acc @ CE vEnv fEnv e @ [STI; INCSP -1]
        | Return(o)       -> match o with   
                             | Some(v) -> CE vEnv fEnv v @ [RET (snd vEnv)]
                             | None    -> [RET (snd vEnv - 1)]
        | Alt (gc)        -> let endLabel = newLabel()
                             alt' vEnv fEnv endLabel gc @ 
                             [STOP] @
                             [Label endLabel]
        | Do (gc)         -> let startLabel = newLabel()
                             [Label startLabel] @
                             do' vEnv fEnv startLabel gc                       
        | Block([], stms) -> CSs vEnv fEnv stms
        | _               -> failwith "CS: this statement is not supported yet"
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

    let rec CD vEnv fEnv = function
        | VarDec (_, s) -> let (vEnvMap, _) = vEnv
                           let addr = match Map.tryFind s vEnvMap with
                                      | Some ((v, _)) -> match v with
                                                         | GloVar a -> a
                                                         | LocVar a -> a
                                      | None          -> failwith ("CD: Could not find variable '" + s + "' in vEnv")
                           [CSTI addr; LDI]
        | FunDec (_, s, decs, stm) -> let label = match Map.tryFind s fEnv with
                                                  | Some (label', opt, t) -> label'
                                                  | None                  -> failwith ("CD: Could not find function '" + s + "' in fEnv")
                                      [GOTO label] @
                                      CDs vEnv fEnv decs @
                                      CS vEnv fEnv stm
    and CDs vEnv fEnv decs = List.collect (CD vEnv fEnv) decs
                          

    
    (* ------------------------------------------------------------------- *)
    
    (* Build environments for global variables and functions *)
 
    

    let makeGlobalEnvs decs = 
        let decv = function
            | VarDec (t, s)       -> (t, s)
            | FunDec (o, s, _, _) -> match o with
                                     | Some(t) -> (t, s)
                                     | None    -> (ITyp, s) // if no type is returned, 
                                                            // int is implicity returned                                        
        let rec addv decs vEnv (fEnv : funEnv) = 
            match decs with
            | []         -> (vEnv, fEnv, [])
            | dec::decr  -> match dec with
                            | VarDec (typ, var)        -> let (vEnv1, code1) = allocate GloVar (typ, var) vEnv
                                                          let (vEnv2, fEnv2, code2) = addv decr vEnv1 fEnv
                                                          (vEnv2, fEnv2, code1 @ code2)
                            | FunDec (tyOpt, f, xs, _) -> addv decr vEnv (fEnv.Add(f, (newLabel(), tyOpt, List.map decv xs)))
        addv decs (Map.empty, 0) Map.empty

    /// CP prog gives the code for a program prog
    let CP (P(decs, stms)) = 
       let _ = resetLabels ()
       let ((gvM, _) as gvEnv, fEnv, initCode) = makeGlobalEnvs decs
       initCode @ CSs gvEnv fEnv stms @ [STOP]
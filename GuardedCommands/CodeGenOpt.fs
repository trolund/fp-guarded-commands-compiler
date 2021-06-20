namespace GuardedCommands.Backend
// Michael R. Hansen 05-01-2016, 04-01-2018, 07-01-2021
// A part of the program is directly copied from the file 
// File MicroC/Contcomp.fs of the MicroC compiler by Peter Sestoft

open Machine
open GuardedCommands.Frontend.AST

module CodeGenerationOpt =

   type Var = 
     | GloVar of int                   (* absolute address in stack           *)
     | LocVar of int                   (* address relative to bottom of frame *)

(* The variable environment keeps track of global and local variables, and 
   keeps track of next available offset for local variables *)
   type varEnv = Map<string, Var * Typ> * int

(* The function environment maps function name to label and parameter decs *)
   type ParamDecs = (Typ * string) list
   type funEnv = Map<string, label * Typ option * ParamDecs>

   let addLocVar vEnv (t, s) = let (vEnv', fdepth) = vEnv
                               ((Map.add s (LocVar fdepth, t) vEnv'), fdepth + 1)

   let addLocVars vEnv p = 
        List.fold addLocVar vEnv p

   let lookupFun fEnv s =
        match Map.tryFind s fEnv with
        | None    -> failwith ("lookup: "+s+" not found.")
        | Some(x) -> x

   let lookupVar vEnv s =
        let (vEnv', _) = vEnv
        match Map.tryFind s vEnv' with
        | None    -> failwith ("lookup: "+s+" not found.")
        | Some(x) -> x

(* Directly copied from Peter Sestoft   START  
   Code-generating functions that perform local optimizations *)
   let rec addINCSP m1 C : instr list =
       match C with
       | INCSP m2            :: C1 -> addINCSP (m1+m2) C1
       | RET m2              :: C1 -> RET (m2-m1) :: C1
       | Label lab :: RET m2 :: _  -> RET (m2-m1) :: C
       | _                         -> if m1=0 then C else INCSP m1 :: C

   let addLabel C : label * instr list =          (* Conditional jump to C *)
       match C with
       | Label lab :: _ -> (lab, C)
       | GOTO lab :: _  -> (lab, C)
       | _              -> let lab = newLabel() 
                           (lab, Label lab :: C)

   let makeJump C : instr * instr list =          (* Unconditional jump to C *)
       match C with
       | RET m              :: _ -> (RET m, C)
       | Label lab :: RET m :: _ -> (RET m, C)
       | Label lab          :: _ -> (GOTO lab, C)
       | GOTO lab           :: _ -> (GOTO lab, C)
       | _                       -> let lab = newLabel() 
                                    (GOTO lab, Label lab :: C)

   let makeCall m lab C : instr list =
       match C with
       | RET n            :: C1 -> TCALL(m, n, lab) :: C1
       | Label _ :: RET n :: _  -> TCALL(m, n, lab) :: C
       | _                      -> CALL(m, lab) :: C

   let rec deadcode C =
       match C with
       | []              -> []
       | Label lab :: _  -> C
       | _         :: C1 -> deadcode C1

   let addNOT C =
       match C with
       | NOT        :: C1 -> C1
       | IFZERO lab :: C1 -> IFNZRO lab :: C1 
       | IFNZRO lab :: C1 -> IFZERO lab :: C1 
       | _                -> NOT :: C

   let addJump jump C =                    (* jump is GOTO or RET *)
       let C1 = deadcode C
       match (jump, C1) with
       | (GOTO lab1, Label lab2 :: _) -> if lab1=lab2 then C1 
                                         else GOTO lab1 :: C1
       | _                            -> jump :: C1
    
   let addGOTO lab C = addJump (GOTO lab) C

   let rec addCST i C =
       match (i, C) with
       | (0, ADD        :: C1) -> C1
       | (0, SUB        :: C1) -> C1
       | (0, NOT        :: C1) -> addCST 1 C1
       | (_, NOT        :: C1) -> addCST 0 C1
       | (1, MUL        :: C1) -> C1
       | (1, DIV        :: C1) -> C1
       | (0, EQ         :: C1) -> addNOT C1
       | (_, INCSP m    :: C1) -> if m < 0 then addINCSP (m+1) C1
                                  else CSTI i :: C
       | (0, IFZERO lab :: C1) -> addGOTO lab C1
       | (_, IFZERO lab :: C1) -> C1
       | (0, IFNZRO lab :: C1) -> C1
       | (_, IFNZRO lab :: C1) -> addGOTO lab C1
       | _                     -> CSTI i :: C
            
(* ------------------------------------------------------------------- *)

(* End code directly copied from Peter Sestoft *)

   let rec repeat n (s: int -> list<'a>) acc =
        match n with 
        | 0 -> acc
        | _ -> repeat (n-1) s (acc @ (s n)) 


/// CE e vEnv fEnv k gives the code for an expression e on the basis of a variable and a function environment and continuation k
   let rec CE e vEnv fEnv k = 
       match e with
       | N n            -> addCST n k
       | B b            -> addCST (if b then 1 else 0) k
       | Access acc     -> CA acc vEnv fEnv (LDI :: k) 
       | Addr acc       -> CA acc vEnv fEnv k
       | Apply("-",[e]) -> CE e vEnv fEnv (addCST 0 (SWAP:: SUB :: k))
       | Apply("!",[b]) -> CE b vEnv fEnv (addNOT k)
       | Apply(o,[b1;b2]) when List.exists (fun x -> o=x) ["&&";"<>";"||"] -> 
                match o with
                | "&&" ->
                        match k with
                        | IFZERO lab :: _ -> CE b1 vEnv fEnv (IFZERO lab :: CE b2 vEnv fEnv k)
                        | IFNZRO labthen :: k1 -> 
                                let (labelse, k2) = addLabel k1
                                CE b1 vEnv fEnv
                                     (IFZERO labelse :: CE b2 vEnv fEnv (IFNZRO labthen :: k2))
                        | _ ->  let (jumpend,  k1) = makeJump k
                                let (labfalse, k2) = addLabel (addCST 0 k1)
                                CE b1 vEnv fEnv (IFZERO labfalse :: CE b2 vEnv fEnv (addJump jumpend k2))
                | "<>" -> CE b1 vEnv fEnv (CE b2 vEnv fEnv (EQ::addNOT(k)))
                | "||" ->
                        match k with
                        | IFNZRO lab :: _ -> CE b1 vEnv fEnv (IFNZRO lab :: CE b2 vEnv fEnv k)
                        | IFZERO labthen :: k1 ->
                                let (labelse, k2) = addLabel k1
                                CE b1 vEnv fEnv
                                      (IFNZRO labelse :: CE b2 vEnv fEnv (IFZERO labthen :: k2))
                        | _ -> let (jumpend,  k1) = makeJump k
                               let (labfalse, k2) = addLabel (addCST 1 k1)
                               CE b1 vEnv fEnv (IFNZRO labfalse :: CE b2 vEnv fEnv (addJump jumpend k2))
                | _    -> failwith "CE: this should not happen"
       | Apply(o,[e1;e2])  when List.exists (fun x -> o=x) ["+"; "-"; "*"; "/"; "%"; "="; "<"; ">"; "<="; ">="]
                          -> let ins = match o with
                                       | "+"  -> ADD::k
                                       | "-"  -> SUB::k
                                       | "*"  -> MUL::k
                                       | "/"  -> DIV::k
                                       | "%"  -> MOD::k
                                       | "="  -> EQ::k
                                       | "<"  -> LT::k
                                       | ">"  -> SWAP::LT::k
                                       | "<=" -> SWAP::LT::addNOT(k)
                                       | ">=" -> LT::addNOT(k)
                                       | _    -> failwith "CE: this case is not possible"
                             CE e1 vEnv fEnv (CE e2 vEnv fEnv ins) 
       | Apply(f,es)      -> call f es vEnv fEnv k
       | Ternary(b, t, f) ->  let labend = newLabel()
                              let labfalse = newLabel()
                              CE b vEnv fEnv (IFZERO labfalse :: CE t vEnv fEnv (GOTO labend :: Label labfalse :: CE f vEnv fEnv (Label labend :: k)))
       | PreInc(i,a)        -> CA a vEnv fEnv (DUP::LDI::(addCST i (ADD::STI::k)))  
       | _                -> failwith "CE: not supported yet"
       
   and CEs es vEnv fEnv k = 
      match es with 
      | []     -> k
      | e::es' -> CE e vEnv fEnv (CEs es' vEnv fEnv k) 
   
   and call f es vEnv fEnv k =
      let (label, _, p) = lookupFun fEnv f
      CEs es vEnv fEnv (makeCall (List.length p) label k)

/// CA acc vEnv fEnv k gives the code for an access acc on the basis of a variable and a function environment and continuation k
   and CA acc vEnv fEnv k = 
      match acc with 
      | AVar x         -> match Map.find x (fst vEnv) with
                          | (GloVar addr,_) -> addCST addr k
                          | (LocVar addr,_) -> GETBP::(addCST addr (ADD::k))
      | AIndex(acc, e) -> CA acc vEnv fEnv (LDI::(CE e vEnv fEnv (ADD::k)))
      | ADeref e       -> CE e vEnv fEnv k
   and CAs accs vEnv fEnv k =
      match accs with
      | [] -> k
      | acc::accs' -> CA acc vEnv fEnv (CAs accs' vEnv fEnv k)
   
(* Bind declared variable in env and generate code to allocate it: *)  
   let allocate (kind : int -> Var) (typ, x) (vEnv : varEnv)  =
    let (env, fdepth) = vEnv 
    match typ with
    | ATyp (ATyp _, _) -> raise (Failure "allocate: array of arrays not permitted")
    | ATyp (t, Some i) -> let newEnv = (Map.add x (kind (fdepth + i), typ) env, fdepth + i + 1)
                          let code = addINCSP i (GETSP :: addCST (i - 1) [SUB])
                          (newEnv, code)
    | _                -> let newEnv = (Map.add x (kind fdepth, typ) env, fdepth+1)
                          let code = [INCSP 1]
                          (newEnv, code)
                      
/// CS s vEnv fEnv k gives the code for a statement s on the basis of a variable and a function environment and continuation k                            
   let rec CS stm vEnv fEnv k = 
       match stm with
       | PrintLn e         -> CE e vEnv fEnv (PRINTI:: INCSP -1 :: k)
       | Ass([acc],[e])    -> CA acc vEnv fEnv (CE e vEnv fEnv (STI:: addINCSP -1 k))
       | Ass(accs,es)      -> let n = es.Length
                              // CEs es vEnv fEnv k @ CAs accs vEnv fEnv k @ repeat n (fun x -> [GETSP; CSTI (x-1); SUB; LDI; GETSP; CSTI (n+x); SUB; LDI; STI; INCSP -1]) [] @ [INCSP -(n*2)]
                              let shiftReduce = repeat n (fun x -> [GETSP; CSTI (x-1); SUB; LDI; GETSP; CSTI (n+x); SUB; LDI; STI; INCSP -1]) []
                              CEs es vEnv fEnv (CAs accs vEnv fEnv (shiftReduce @ addINCSP (-(n*2)) k)) 
       | Return(o)         -> match o with
                              | Some(v) -> CE v vEnv fEnv (RET (snd vEnv)::k)
                              | None    -> RET (snd vEnv - 1)::k
       | Block([],stms)    -> CSs stms vEnv fEnv k
       | Block(decs, stms) -> let (vEnv', code) = compileLocalDecs (vEnv, []) decs
                              code @ CSs stms vEnv' fEnv (addINCSP (snd vEnv - snd vEnv') k) // TODO: still uses append?
       | Alt(gc)           -> let (endlabel,k2) = addLabel k
                              gc' gc vEnv fEnv endlabel (STOP::k2)
       | Do(gc)            -> let startLabel = newLabel() // Regular label since no lookahead
                              Label startLabel::(gc' gc vEnv fEnv startLabel k)
       | Call (f, es)      -> call f es vEnv fEnv (addINCSP (-1) k)
                                                          
   and CSs stms vEnv fEnv k = 
        match stms with
        | []   -> k
        | stm::stms' -> CS stm vEnv fEnv (CSs stms' vEnv fEnv k)
   
   and gc' gc vEnv fEnv el k =
        match gc with
        | GC([]) -> k
        | GC ((b,stms)::alts) -> let (labnext,k2) = addLabel (gc' (GC(alts)) vEnv fEnv el k)
                                 CE b vEnv fEnv ((IFZERO labnext)::(CSs stms vEnv fEnv (addGOTO el k2)))

   and compileLocalDec vEnv = function
        | VarDec (t, s) -> allocate LocVar (t, s) vEnv
        | FunDec _      -> (vEnv, [])
   and compileLocalDecs (vEnv, code) = function
        | []            -> (vEnv,code)
        | d::ds         -> let (vEnv', code') = compileLocalDec vEnv d
                           compileLocalDecs (vEnv', code @ code') ds

   and compileFunc vEnv fEnv = function
        | VarDec _              -> []
        | FunDec (_, s, _, stm) -> let vEnv' = (fst vEnv, 0)
                                   let (label, _, p) = lookupFun fEnv s
                                   let localvEnv = addLocVars vEnv' p
                                   Label label::(CS stm localvEnv fEnv [RET (List.length p - 1)])                      
   and compileFuncs vEnv fEnv decs = 
        List.collect (compileFunc vEnv fEnv) decs

(* ------------------------------------------------------------------- *)

(* Build environments for global variables and functions *)
   let makeGlobalEnvs decs = 
       let decv = function
           | VarDec (t,s) -> (t,s)
           | FunDec _     -> failwith "decv: A function parameter can not be a unction itself"

       let rec addv decs vEnv fEnv = 
           match decs with 
           | []         -> (vEnv, fEnv, [])
           | dec::decr  -> 
             match dec with
             | VarDec (typ, var) -> let (vEnv1, code1) = allocate GloVar (typ, var) vEnv
                                    let (vEnv2, fEnv2, code2) = addv decr vEnv1 fEnv
                                    (vEnv2, fEnv2, code1 @ code2)
             | FunDec (tyOpt, f, xs, _) -> addv decr vEnv (Map.add f ((newLabel(), tyOpt, List.map decv xs)) fEnv)
       addv decs (Map.empty, 0) Map.empty

(* CP compiles a program *)
   let CP (P(decs,stms)) = 
       let _ = resetLabels ()
       let ((gvM,_) as gvEnv, fEnv, initCode) = makeGlobalEnvs decs
       initCode @ CSs stms gvEnv fEnv (STOP::(compileFuncs gvEnv fEnv decs))
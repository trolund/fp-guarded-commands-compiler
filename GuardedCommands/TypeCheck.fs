namespace GuardedCommands.Frontend
// Michael R. Hansen 06-01-2016 , 04-01-2018, 07-06 2021

open GuardedCommands.Frontend.AST

module TypeCheck = 

   //Helper functions

   //Compare types between function declaration and function application
   let rec compareTypes xl yl =
      match xl, yl with 
      | [], []       -> true
      | [], y::ys    -> false
      | x::xs, []    -> false
      | x::xs, y::ys -> x = y && compareTypes xs ys

/// tcE gtenv ltenv e gives the type for expression e on the basis of type environments gtenv and ltenv
/// for global and local variables 
   let rec tcE gtenv ltenv = function                            
         | N _              -> ITyp   
         | B _              -> BTyp   
         | Access acc       -> tcA gtenv ltenv acc     
                   
         | Apply(f,[e]) when List.exists (fun x ->  x=f) ["-"; "!"]  
                            -> tcMonadic gtenv ltenv f e        

         | Apply(f,[e1;e2]) when List.exists (fun x ->  x=f) ["+"; "-"; "*"; "/"; "%";"="; "<="; ">="; "<>"; "<"; ">"; "&&"; "||"]        
                            -> tcDyadic gtenv ltenv f e1 e2   
         | Apply(f, es)     -> tcNaryFunction gtenv ltenv f es
         | _                -> failwith "tcE: not supported yet"

   and tcMonadic gtenv ltenv f e = match (f, tcE gtenv ltenv e) with
                                   | ("-", ITyp) -> ITyp
                                   | ("!", BTyp) -> BTyp
                                   | _           -> failwith "illegal/illtyped monadic expression" 
   
   and tcDyadic gtenv ltenv f e1 e2 = match (f, tcE gtenv ltenv e1, tcE gtenv ltenv e2) with
                                      | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) ["+";"-";"*";"/";"%"]  -> ITyp
                                      | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) ["=";"<=";">=";"<>";"<";">"] -> BTyp
                                      | (o, BTyp, BTyp) when List.exists (fun x ->  x=o) ["=";"<>";"&&";"||"]     -> BTyp 
                                      | _                      -> failwith("illegal/illtyped dyadic expression: " + f)

   and tcNaryFunction gtenv ltenv f es = let fType = Option.get(Map.tryFind f gtenv)
                                         //Convert expression list to type list
                                         let expList = List.rev (List.fold (fun acc e -> tcE gtenv ltenv e::acc) [] es)
                                         
                                         //Return function type (i.e. return type) if the expression list' type matches the declaration type
                                         match fType with
                                          | FTyp(tl, Some(t)) -> if not (compareTypes tl expList) then failwith "Invalid argument types"
                                                                 else t
                                          | _                 -> failwith "invalid function application type"
   
   //failwith "type check: functions not supported yet"
 
   and tcNaryProcedure gtenv ltenv f es = failwith "type check: procedures not supported yet"
      

/// tcA gtenv ltenv e gives the type for access acc on the basis of type environments gtenv and ltenv
/// for global and local variables 
   and tcA gtenv ltenv = 
         function 
         | AVar x         -> match Map.tryFind x ltenv with
                             | None   -> match Map.tryFind x gtenv with
                                         | None   -> failwith ("no declaration for : " + x)
                                         | Some t -> t
                             | Some t -> t            
         | AIndex(acc, e) ->
                           if (tcE gtenv ltenv e) <> ITyp
                           then failwith "tcA: adressing using non-integer expression"
                           match tcA gtenv ltenv acc with
                              ATyp(t',_) -> t'
                              | _ -> failwith "tcA: adressing non-array variable"
         | ADeref e       -> failwith "tcA: pointer dereferencing not supported yes"
 

/// tcS gtenv ltenv s checks the well-typeness of a statement s on the basis of type environments gtenv and ltenv
/// for global and local variables 
   and tcS gtenv ltenv = function                           
                         | PrintLn e -> ignore(tcE gtenv ltenv e)
                         | Ass(acc,e) -> if tcA gtenv ltenv acc = tcE gtenv ltenv e 
                                         then ()
                                         else failwith "illtyped assignment"                          
                         | Alt gc -> tcGC gtenv ltenv gc
                         | Do gc -> tcGC gtenv ltenv gc
                         | Block([],stms) -> List.iter (tcS gtenv ltenv) stms
                         | Block(_, _)    -> failwith "Local declaration has to be assigned to a function/procedure declaration"
                         | Call(name, exps)  -> failwith "procedure not defined"
                                                //match fType with
                                                //   | None    -> failwith "function/procedure not defined"
                                                //   | Some(FTyp(tl, None))    -> ()
                                                //   | Some(FTyp(tl, Some(t))) -> let expList = List.rev (List.fold (fun acc e -> tcE gtenv ltenv e::acc) [] exps)
                                                //                                if compareTypes tl expList //Match element by element if they have the same type
                                                //                                then ()

                         // TODO: Call
                         | _              -> failwith "tcS: this statement is not supported yet"
   and tcGC gtenv ltenv = function
      | GC(l) -> 
                  if List.exists (fun (e,_) -> tcE gtenv ltenv e <> BTyp) l
                  then failwith "type check: illtyped boolean expression in guarded command"
                  List.iter (fun (_,sl) -> List.iter (tcS gtenv ltenv) sl) l
   and tcGDec gtenv = function  
                      | VarDec(ATyp(t,i),_) when not(t=ITyp || t=BTyp) || i = None || Option.get(i) < 1 -> failwith "type check: illtyped array declaration"
                      | VarDec(t,s)               -> Map.add s t gtenv
                      | FunDec(t,f, decs, stm) ->
                           // Parameters should be different
                           let paramTest = List.distinctBy (function VarDec(t,s) -> s | _ -> failwith "tcS parameter fail") decs
                           if List.length paramTest <> List.length decs
                           then failwith "tcDec parameters should be distinct"
                           // Make new type-environment
                           //    Include every parameter
                           //    Include function itself
                           let ltenv' = List.fold tcFunDec Map.empty decs
                           let gtenv' = Map.add f (FTyp((List.choose (function VarDec(t',_) -> Some(t') | _ -> None)) decs,t)) gtenv
                           // Check every return statement has type t
                           // Check stm is well-typed
                           if not (tcFunBod gtenv' ltenv' t stm) && t <> None
                           then failwith "type check: function body missing return statement"
                           gtenv'
   and tcFunDec ltenv = function
      | VarDec(ATyp(t,i),_) when not(t=ITyp || t=BTyp) || i <> None -> failwith "type check: faulty array declaration in function parameter"
      | VarDec(t,s) -> Map.add s t ltenv
      | _ -> failwith "type check: faulty parameter in function declaration"
   and tcFunBod gtenv ltenv t = function
      | Block(decs, stmts) -> let ltenv' = tcLDecs (ltenv) decs
                              List.fold (fun seen stmt -> tcFunStm gtenv ltenv' t stmt || seen) false stmts
      | stm -> tcFunStm gtenv ltenv t stm
   and tcFunStm gtenv ltenv t = function
                                | Return(Some(t')) when t<> None && Option.get(t)=(tcE gtenv ltenv t') -> true
                                | Return(None) when t=None -> true
                                | Return(_) -> failwith "type check: return type mismatch"
                                | Do(GC(l)) | Alt(GC(l)) ->
                                                        if List.exists (fun (e,_) -> tcE gtenv ltenv e <> BTyp) l
                                                        then failwith "type check: illtyped boolean expression in guarded command"
                                                        List.fold (fun seen (_,stml) -> List.fold (fun seen' stmt -> tcFunStm gtenv ltenv t stmt || seen') false stml || seen ) false l
                                | s -> tcS gtenv ltenv s
                                       false
   and tcGDecs gtenv = function
                       | dec::decs -> tcGDecs (tcGDec gtenv dec) decs
                       | _         -> gtenv
   //Typechecking local env
   and tcLDec ltenv = function
      | VarDec(t,s)  -> Map.add s t ltenv
      | FunDec(_)    -> failwith "function declaration not allowed in block"
   and tcLDecs ltenv = function
      | dec::decs    -> tcLDecs (tcLDec ltenv dec) decs
      | _            -> ltenv
   


/// tcP prog checks the well-typeness of a program prog
   and tcP(P(decs, stms)) = let gtenv = tcGDecs Map.empty decs
                            List.iter (tcS gtenv Map.empty) stms

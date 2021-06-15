namespace Tree

open GuardedCommands.Frontend.AST

module TreeManager =

    type 'a Tree = Node of 'a * ('a Tree list)
    type Extent = (float * float) list

    let rec same' x y =
        match x,y with
        | Node((_,x'),[]),Node((_,y'),[]) when x'=y'-> true
        | Node((_,x'),xs),Node((_,y'),ys) when x'=y' -> List.length xs = List.length ys && List.forall2 same' xs ys
        | _,_ -> false
    let rec same (Node(_,x)) (Node(_,y)) = List.length x = List.length y && List.forall2 same' x y


    let rec similar x y =
        match x,y with
        | Node(_,[]), Node(_,[]) -> true
        | Node(_,xs),Node(_,ys) -> List.length xs = List.length ys && List.forall2 similar xs ys


    let movetree (Node ((label, x), subtrees), x': float) =
        Node((label, x + x'), subtrees)


    let moveextent (e, x) =
        List.map (fun (p, q) -> (p + x, q + x)) e


    let rec merge ps qs =
        match (ps, qs) with
        | ([], qs)                     -> qs
        | (ps, [])                     -> ps
        | ((p, _) :: ps, (_, q) :: qs) -> (p, q) :: merge ps qs


    let mergelist es = 
        List.fold merge [] es


    let rmax (p: float, q: float) = 
        if p > q then p else q


    let rec fit =
        function
        | ((_, p) :: ps), ((q, _) :: qs) -> rmax (fit (ps, qs), p - q + 1.0)
        | _                              -> 0.0


    let fitlistl es =
        let rec fitlistl' acc =
            function
            | []      -> []
            | e :: es ->
                let x = fit (acc, e)
                x :: fitlistl' (merge acc (moveextent (e, x))) es
        fitlistl' [] es


    // val flipextent : Extent -> Extent = map (fn (p,q) => (~q,~p))
    let flipextent e =
        List.map (fun (p, q) -> (-q, -p)) e


    // val fitlistr = rev o map ~ o fitlistl o map flipextent o rev
    // let fitlistr (es: Extent list) =
    //    List.rev (List.map (-) (fitlistl (List.map flipextent (List.rev es))));;
    let fitlistr (es: Extent list) =
        List.rev es
        |> List.map flipextent
        |> fitlistl
        |> List.map (fun e -> -e)
        |> List.rev


    let mean (x, y) = 
        (x + y) / 2.0


    let fitlist es =
        List.map mean (List.zip (fitlistl es) (fitlistr es))


    let design tree =
        let rec design' (Node (label, subtrees)) =
            let (trees, extents) = List.unzip (List.map design' subtrees)
            let positions = fitlist extents
            let ptrees =
                List.map movetree (List.zip trees positions)
            let pextents =
                List.map moveextent (List.zip extents positions)
            let resultextent = (0.0, 0.0) :: mergelist pextents
            let resulttree = Node((label, 0.0), ptrees)
            (resulttree, resultextent)
        fst (design' tree)


    let rec parseExp e =
        match e with
        | N n           -> Node("Int " + string n, [])
        | B b           -> Node("Bool " + string b, [])
        | Access a      -> parseAccess a
        | Addr a        -> parseAccess a
        | Apply (s, es) -> Node("Apply " + s, parseExpList es)
     and parseExpList es =
        List.map parseExp es
     and parseAccess a =
        match a with
        | AVar s        -> Node("Var \"" + s + "\"", [])
        | AIndex (a, e) -> Node("Index", [parseAccess a; parseExp e])
        | ADeref e      -> Node("Deref", [parseExp e])
    and parseAccessList al = 
        List.map parseAccess al

    let rec parseTyp t =
        match t with
        | ITyp           -> Node("IntTyp", [])
        | BTyp           -> Node("BoolTyp", [])
        | ATyp (t, opt)  -> match opt with
                            | Some(i) -> Node("Array", [parseTyp t] @ [Node (string i, [])])
                            | None    -> Node("Array", [parseTyp t])
        | PTyp t         -> Node ("Pointer", [parseTyp t])
        | FTyp (ts, opt) -> match opt with
                            | Some(t) -> Node("Function", parseTypList ts @ [parseTyp t])
                            | None    -> Node("Function", parseTypList ts)
    and parseTypList ts =
        List.map parseTyp ts

    let rec parseDec d =
        match d with
        | VarDec (t, s)            -> Node ("VarDec", [Node (s, []); parseTyp t])
        | FunDec (opt, s, ds, stm) -> match opt with
                                      | Some(t) -> let nodes = [Node(s, [parseTyp t] @ parseDecList ds @ [parseStm stm])]
                                                   Node("FunDec", nodes)
                                      | None    -> let nodes = [Node(s, parseDecList ds @ [parseStm stm])]
                                                   Node("FunDec", nodes)
    and parseDecList ds = 
        List.map parseDec ds
    and parseStm s =
        match s with
        | PrintLn e        -> Node("PrintLn", [parseExp e])
        | Ass (a, e)       -> Node("Ass", parseAccessList a @ parseExpList e)
        | Return opt       -> match opt with
                              | Some(e) -> Node("Return", [parseExp e])
                              | None    -> Node("Return", [])
        | Alt gc           -> Node("Alt", [parseGc gc])
        | Do gc            -> Node("Do", [parseGc gc])
        | Block (ds, ss)   -> Node("Block", parseDecList ds @ parseStmList ss)
        | Call (s, es)     -> Node("Call " + s, parseExpList es)
    and parseStmList ss =
        List.map parseStm ss
    and parseGc gc =
        match gc with
        | GC ([])            -> failwith "Empty GuardedCommand!"
        | GC (((e, ss)::[])) -> Node("Guarded Command", [parseExp e] @ parseStmList ss)
        | GC ((e, ss)::gs)   -> Node("Guarded Command", [parseExp e] @ parseStmList ss @ [parseGcList gs])
    and parseGcList gs =
        parseGc (GC gs)

    let parseProgram p =
        match p with
        | P (ds, ss) -> Node ("Program", parseDecList ds @ parseStmList ss)                     

    let toGeneralTree p =
        parseProgram p
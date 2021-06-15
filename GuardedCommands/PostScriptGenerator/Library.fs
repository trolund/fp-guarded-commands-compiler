namespace PostScriptGenerator

open FPP1.TreeManager
open System.IO
open System.Text

module Generator =

    // global settings
    let startX       = 0.0
    let startY       = -20.0

    let parentMargin = 10.0
    let nodeHeight   = 20.0
    let nodeWidth    = 50.0
    let depthHeight  = 50.0
    let depthMargin  = 16.0
    let labelMargin  = 10.0

    let psPre        = "%!\n<</PageSize[1400 1000]/ImagingBBox null>> setpagedevice\n1 1 scale\n700 999 translate\nnewpath\n/Times-Roman findfont 10 scalefont setfont\n"
    let showpage     = "showpage"
    let stroke       = "stroke\n"


    let positionX x pos =
        match pos with
        | 0.0 -> x
        | _   -> x + pos * nodeWidth


    let rec subtreeWidth ts =
        match ts with 
        | []                      -> 0.0
        | Node ((_, pos), _)::[]  -> abs pos * nodeWidth
        | Node ((_, pos), _)::ts' -> let (Node((_, pos'), _)) = List.last ts'
                                     (abs pos + abs pos') * nodeWidth


    let rec mostLabelSpaces ts = 
        match ts with
        | []                  -> 0.0
        | Node((l, _), _)::ts -> let spaces = float (List.length ((string l).Split(' ') |> Array.toList))
                                 max spaces (mostLabelSpaces ts)


    let rec labelSpaceList curr next acc =
        match curr, next with
        | [], []               -> []
        | Node(_, ts)::ts', [] -> labelSpaceList ts' ts (mostLabelSpaces ts)
        | [], l                -> acc :: (labelSpaceList l [] 0.0)
        | Node(_, ts)::ts', l  -> labelSpaceList ts' (l @ ts) (max acc (mostLabelSpaces ts))
                              

    let toPSslow t =
        let moveto x y = 
            string x + " " + string y + " moveto\n"
         

        let lineto x y = 
            string x + " " + string y + " lineto\n"


        let label l 
            = "(" + string l + ") dup stringwidth pop 2 div neg 0 rmoveto show\n"

            
        let makeLabel (l:string) x y = 
            let ls = l.Split(' ') |> Array.toList
            let rec makeLabel' ls x y = 
                match ls with
                | []    -> ""
                | l::ls -> moveto x y + label l + makeLabel' ls x (y - labelMargin)
            makeLabel' ls x y

                                       
        let rec subtreeLines ts x y =
            match ts with
            | []                     -> ""
            | Node ((_, pos), _)::ts -> let x' = positionX x pos 
                                        moveto x' y + lineto x' (y - depthHeight) + subtreeLines ts x y

                                        
        let rec psTree t x y sl =
            match t with
            | Node ((l, _), []) -> makeLabel (string l) x y
            | Node ((l, _), ts) -> let out = moveto x y
                                   //let y = y - parentMargin
                                   let out = out + (makeLabel l x y)
                                   let (spaces, sls) =
                                        match sl with
                                        | [] -> 1.0 , []
                                        | h :: slt -> h , slt
                                   let y = y - spaces * labelMargin
                                   let out = out + moveto x y
                                   let y = y - nodeHeight
                                   let out = out + lineto x y
                                   let lineWidth = subtreeWidth ts
                                   let halfLineWidth = lineWidth / 2.0
                                   let x = x - halfLineWidth
                                   let out = out + moveto x y
                                   let x = x + lineWidth
                                   let out = out + lineto x y + stroke
                                   let x = x - halfLineWidth
                                   let out = out + subtreeLines ts x y + psSubtrees ts x (y - depthHeight - depthMargin) sls
                                   out
        and psSubtrees ts x y sl =
            match ts with
            | []     -> ""
            | t::ts' -> let (Node((_, pos), _)) = t
                        let x' = positionX x pos
                        psTree t x' y sl + psSubtrees ts' x y sl
                           
        psPre + psTree t startX startY (labelSpaceList [t] [] 0.0) + stroke + showpage


    let toPSfast t =
        let moveto x y =
            String.concat " " [ string x; string y; "moveto\n" ]


        let lineto x y =
            String.concat " " [ string x; string y; "lineto\n" ]


        let label l = 
            String.concat "" [ "("; string l; ") dup stringwidth pop 2 div neg 0 rmoveto show\n" ]


        let makeLabel (l:string) x y = 
            let ls = l.Split(' ') |> Array.toList
            let rec makeLabel' ls x y = 
                match ls with
                | []    -> ""
                | l::ls -> String.concat "" [moveto x y; label l; makeLabel' ls x (y - labelMargin)]
            makeLabel' ls x y
           
                                       
        let rec subtreeLines ts x y =
            match ts with
            | []                     -> ""
            | Node ((_, pos), _)::ts -> let x' = positionX x pos 
                                        String.concat "" [moveto x' y; lineto x' (y - depthHeight); subtreeLines ts x y]
   

        let rec psTree t x y sl =
            match t with
            | Node((l, _), []) -> makeLabel (string l) x y
            | Node((l, _), ts) ->   let sb = new StringBuilder()
                                    sb.Append (moveto x y) |> ignore
                                    //let y = y - parentMargin
                                    sb.Append (makeLabel l x y)|> ignore
                                    let (spaces, sls) =
                                        match sl with
                                        | [] -> 1.0 , []
                                        | h :: slt -> h , slt
                                    let y = y - spaces * labelMargin
                                    sb.Append (moveto x y) |> ignore
                                    let y = y - nodeHeight
                                    sb.Append (lineto x y) |> ignore
                                    let lineWidth = subtreeWidth ts
                                    let halfLineWidth = lineWidth / 2.0
                                    let x = x - halfLineWidth
                                    sb.Append (moveto x y) |> ignore
                                    let x = x + lineWidth
                                    sb.Append (lineto x y) |> ignore
                                    sb.Append (stroke) |> ignore
                                    let x = x - halfLineWidth
                                    sb.Append (subtreeLines ts x y) |> ignore
                                    sb.Append (psSubtrees ts x (y - depthHeight - depthMargin) sls : string) |> ignore
                                    sb.ToString()
        and psSubtrees ts x y sl =
            match ts with 
            | []     -> ""
            | t::ts' -> let (Node((_, pos), _)) = t
                        let x' = positionX x pos
                        String.concat "" [psTree t x' y sl; psSubtrees ts' x y sl]
                           
        String.concat "" [psPre; psTree t startX startY (labelSpaceList [t] [] 0.0); stroke; showpage]


    let writeToFile n d =
        File.WriteAllText("../output/" + n + ".ps", d)


    let treeToFile n t =
        writeToFile n (design t |> toPSfast)


    let posTreeToFile n t =
        writeToFile n (toPSfast t)
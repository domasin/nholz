#load "avvio.fsx"
open HOL

open System.IO

CoreThry.load
Equal.load
Bool.load

type InfRule = 
    | NullFun
    | TmFn of (term -> thm)
    | ThmThmFn of (thm -> thm -> thm)
    | ThmFn of (thm -> thm)

type ProofTree = (Exp * string * InfRule) Tree 

let rec treeToLatex2 ntabs (g : Tree<Exp * string * InfRule>) = 
    let tabs = "\t" |> String.replicate ntabs
    match g with
    | Tree((p,s,_),xs) -> 
        match xs with
        | [] -> (p |> printExp) + if s = "" then "" else "\; \mathbf{ " + s + "}"
        | _ -> 
            let prec = 
                xs
                |> List.fold (fun acc x -> (if acc = "" then "" else acc + ("\n"+ tabs + "\qquad\n" + tabs)) + (x |> treeToLatex2 (ntabs+1))) ""
            sprintf "\\dfrac\n%s{%s}\n%s{%s}\n%s\\textsf{ %s}" tabs prec tabs (p |> printExp) tabs s

let view2 loc =
    let proof = loc |> root
    let proofStr = proof |> treeToLatex2 1
    let html = sprintf "<!DOCTYPE html><html><head><script type=\"text/javascript\" src=\"https://cdn.mathjax.org/mathjax/latest/MathJax.js\">MathJax.Hub.Config({ config: [\"TeX-AMS-MML_HTMLorMML.js\"], 	extensions: [\"[a11y]/accessibility-menu.js\"], menuSettings: {	collapsible: true,	autocollapse: true,	explorer: true } });</script></head><body>\\[ \\small{ 	%s } \\]</body></html>" proofStr
    let path = System.IO.Path.GetTempFileName() + ".html"
    let mutable file = File.CreateText(path)
    file.WriteLine(html)
    file.Flush()
    System.Diagnostics.Process.Start(@"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",path) |> ignore
    loc

let proove loc = 
    let (Loc(Tree((ex,label,just_fn),children), path)) = loc

    match ex with
    | Goal(asl,t) ->
        let child = (Loc (Tree ((Goal (asl,t), label,just_fn),children),path)) |> down
        
        match just_fn with
        | TmFn f -> 
            match child with
            | (Loc (Tree ((Te t, "", NullFun),[]),p)) -> 
                loc |> change (Tree ((Th (f t), label, just_fn),children))
            | _ -> failwith "child is not term"
        | ThmFn f -> 
            match child with
            | (Loc (Tree ((Th t, _, _),_),_)) -> 
                loc |> change (Tree ((Th (f t), label, just_fn),children))
            | _ -> failwith "child is not thm"
        | ThmThmFn f -> 
            let child2 = child |> right
            match child with
            | (Loc (Tree ((Th t, _, _),_),_)) -> 
                match child2 with
                | (Loc (Tree ((Th t2, _, _),_),_)) -> 
                    loc |> change (Tree ((Th (f t t2), label, just_fn),children))
                | _ -> failwith "child2 is not thm"
            | _ -> failwith "child1 is not thm"
        | NullFun -> failwith "no rule given"
        
    | _ -> failwith "not a goal"

let refl_conv_bk loc = 
    let (Loc(Tree((ex,label,just_fn),children), path)) = loc
    match ex with
    | Goal(asl,t) ->
        let (ant,_) = dest_eq t
        loc
        |> change (Tree ((Goal (asl,t), "refl_conv", (TmFn refl_conv)),children))
        |> insert_down (mkTree((Te ant),"", NullFun) []) 
    | _ -> failwith "not a goal"

let eq_mp_rule_bk g2 loc = 
    let (Loc(Tree((ex,label,just_fn),children), path)) = loc
    match ex with
    | Goal(asl,t) ->
        match g2 with
        | Goal(asl2,t2) -> 
            let asl1 = 
                asl |> List.filter (fun x -> not (asl2 |> List.contains x))
            let g1 = Goal (asl1,(mk_eq (t2,t)))
            loc
            |> change (Tree ((Goal (asl,t), "eq_mp_rule", (ThmThmFn eq_mp_rule)),children))
            |> insert_down (mkTree(g1, "", NullFun) []) 
            |> insert_right (mkTree(g2, "", NullFun) []) 
        | _-> failwith "the given is not a goal"
    | _ -> failwith "not a goal"

let sym_rule_bk loc = 
    let (Loc(Tree((ex,label,just_fn),children), path)) = loc
    match ex with
    | Goal(asl,t) ->
        let (t1,t2) = dest_eq t
        let g1 = Goal (asl,(mk_eq (t2,t1)))
        loc
        |> change (Tree ((Goal (asl,t), "sym_rule", (ThmFn sym_rule)),children))
        |> insert_down (mkTree(g1, "", NullFun) []) 
    | _ -> failwith "not a goal"

let accept thm str loc = 
    let (Loc(Tree((ex,label,just_fn),children), path)) = loc
    match ex with
    | Goal(asl,t) ->
        let (asl1,t2) = dest_thm thm
        if asl1 = asl && t = t2 then
            loc
            |> change (Tree ((Th thm, str, NullFun),children))
        else failwith "don't match"
    | _ -> failwith "not a goal"

let refl_conv_fd t : ProofTree = 
    let th = t |> refl_conv
    mkTree 
        (Th th,"refl_conv", (TmFn refl_conv))
        [ Tree ((Te t,"", NullFun), [])]

let mkGoal asl s = 
    mkTree(Goal (asl,(s |> parse_term)), "",NullFun) []
    
//(parse_term(@"(\(p:bool). p) = \p. p")) |> print_term

//Te (parse_term(@"(\(p:bool). p) = \p. p")) |> printExp

"true" |> mkGoal []
|> zipper
|> eq_mp_rule_bk (Goal([],(parse_term(@"(\(p:bool). p) = \p. p"))))
|> sym_rule_bk
|> accept true_def "true\_def"
|> up |> proove
|> right
|> refl_conv_bk
|> up |> proove
|> left |> up |> proove
|> view2


|> up |> proove
|> root |> view2

let g = ("true" |> parse_term)
//let goal = mkTree(Goal ([],p), "",NullFun) []

//let p = parse_term(@"p = p") 

//view2 <| refl_conv_fd ("p" |> parse_term)

//let goal = mkTree(Goal ([],p), "",NullFun) []

//goal |> view2

//goal |> zipper |> refl_conv_bk |> up |> root |> view2

//goal |> zipper |> refl_conv_bk |> root |> view2

//goal |> zipper |> refl_conv_bk |> up |> proove |> root |> view2


//let tr = 
//    Tree
//        ("x",
//         [Tree ("a",[Tree ("a1",[]); Tree ("a2",[])]);
//          Tree ("b",[Tree ("b1",[]); Tree ("b2",[])]); Tree ("c",[])])

//tr |> zipper |> down |> right |> down |> right |> root

//tr |> zipper |> down  |> down  |> right  |> right
//tr |> zipper |> findNodePath "c" |> Option.get |> root

//tr 
//    |> zipper 
//    |> down 
//    |> down 
//    |> right 
//    |> insert_down (Tree("a2_1",[])) 
//    |> insert_right (Tree("a2_2",[])) 
//    |> root
//    |> zipper
//    |> down
//    |> right //b
//    |> down  //b1
//    |> delete
//    |> root




//type 'a Tree = Tree of 'a * 'a Tree list

//type 'a Path = 
//    | Top 
//    | NodePath of 'a * 'a Tree list * 'a Path * 'a Tree list

//type 'a Location = Loc of 'a Tree * 'a Path

//let mkTree v xs = Tree(v,xs)

//let left (Loc(t, p)) = 
//    match p with
//    | Top -> failwith "left at top"
//    | NodePath(v,l::left, up, right) -> Loc(l, NodePath(v,left, up, t::right))
//    | NodePath(v,[], up, right) -> failwith "left of first"

//let right (Loc(t, p)) = 
//    match p with 
//    | Top -> failwith "right at top"
//    | NodePath(v,left, up, r::right) -> Loc(r, NodePath(v,t::left, up, right))
//    | _ -> failwith "right of last"

//let down (Loc(t, p)) = 
//    match t with
//    | Tree(_,[]) -> failwith "down with Tree"
//    | Tree(v,t1::trees) -> Loc(t1, NodePath(v,[], p, trees))

//let up (Loc(t,p)) = 
//    match p with
//    | Top -> failwith "up of top"
//    | NodePath(v,left,up,right) -> 
//        Loc(Tree(v, ((left |> List.rev)@[t]) @ right),up)

//let rec root (Loc (t, p) as l) = 
//    match p with 
//    | Top -> t
//    | _ -> root (up l) 

//let zipper t = Loc(t, Top)

//let change t (Loc(_, p)) = Loc(t, p)

//let insert_right r (Loc(t, p)) = 
//    match p with
//    | Top -> failwith "insert at top"
//    | NodePath(v,left, up, right) -> Loc(t, NodePath(v,left, up, r::right))

//let insert_left l (Loc(t, p)) =
//    match p with
//    | Top -> failwith "insert at top"
//    | NodePath(v,left, up, right) -> Loc(t, NodePath(v,l::left, up, right))

//let insert_down t1 (Loc(t, p)) = 
//    match t with
//    | Tree (v,[]) -> Loc(t1, NodePath(v,[], p, []))
//    | Tree(v,ss) -> failwith "non empty"

//let delete (Loc(_, p)) =
//    match p with 
//    | Top -> failwith "delete at top"
//    | NodePath(v,left, up, r::right) -> Loc(r, NodePath(v,left, up, right))
//    | NodePath(v,l::left, up, []) -> Loc(l, NodePath(v,left, up, []))
//    | NodePath(v,[], up, []) -> Loc(Tree (v,[]), up)

//let rec findNodePath (x:'a) (zipper:'a Location) =
//    let (Loc(Tree(value,NodePaths), path)) = zipper
//    if value = x then Some zipper
//    else
//        match NodePaths with
//        | [] -> 
//            //printf " |> right "
//            match path with
//            | NodePath(v,left,up,[]) -> None
//            | _ -> zipper |> right |> (findNodePath x)
//        | _ ->
//            //printf " |> down "
//            let down = zipper |> down |> findNodePath x
//            match down with
//            | Some x -> Some x
//            | None -> 
//                //printfn " |> right "
//                zipper |> right |> (findNodePath x)

//(* Safe implementations that don't fail but return 'a Loc option *)
//let safeleft (Loc(t, p)) = 
//    match p with
//    | Top -> None
//    | NodePath(l::left, up, right) -> Some(Loc(l, NodePath(left, up, t::right)))
//    | NodePath([], up, right) -> None

//let saferight (Loc(t, p)) = 
//    match p with 
//    | Top -> None
//    | NodePath(left, up, r::right) -> Some(Loc(r, NodePath(t::left, up, right)))
//    | _ -> None

//let safeup (Loc(t, p)) = 
//    match p with
//    | Top -> None
//    | NodePath (left, up, right) -> Some(Loc(Section((List.rev left) @ (t::right)), up))
   
//let safedown (Loc(t, p)) = 
//    match t with
//    | Tree(_) -> None
//    | Section(t1::trees) -> Some(Loc(t1, NodePath([], p, trees)))
//    | _ -> None

//(*
//let nth_descendent loc =
//  let rec nth_rec = (fun index -> match index with
//                                  | 1 -> down loc
//                                  | n -> if n > 0 then right (nth_rec (n - 1))
//                                         else failwith "n must be +ve")
//  nth_rec
//*)

//(* Test data *)
//let tree = Section[Tree "a"; Section[Tree "b"; Tree "c"]]

////let subexpr = Loc(Tree "*",
////                  NodePath([Tree "c"],
////                        NodePath([Tree "+"; Section [Tree "a"; Tree "*"; Tree "b"]],
////                              Top,
////                              []),
////                        [Tree "d"]))

//let rec treeToLatex ntabs (g : Tree<string>) = 
//    let tabs = "\t" |> String.replicate ntabs
//    match g with
//    | Section(Tree x, xs) -> 
//        match xs with
//        | [] -> (p |> printExp) + if s = "" then "" else "\; \mathbf{ " + s + "}"
//        | _ -> 
//            let prec = 
//                xs
//                |> List.fold (fun acc x -> (if acc = "" then "" else acc + ("\n"+ tabs + "\qquad\n" + tabs)) + (x |> graphToLatex (ntabs+1))) ""
//            sprintf "\\dfrac\n%s{%s}\n%s{%s}\n%s\\textsf{ %s}" tabs prec tabs (p |> printExp) tabs s


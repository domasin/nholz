[<AutoOpen>]
module HOL.ProofUtils

open System.IO

///// proof tree
//type Graph<'a> = 
//    | Graph of 'a * 'a Graph List
//    member x.children = let (Graph(_, xs)) = x in xs
//    member x.value = let (Graph(v, _)) = x in v
//    override x.ToString() = 
//        match x with
//        | Graph(v,[]) -> v.ToString()
//        | Graph(v,xs) -> sprintf "(%O,%O)" v xs

//let mkTree v xs = Graph(v,xs)

// generic tree
type 'a Tree = Tree of 'a * 'a Tree list

type 'a Path = 
    | Top 
    | NodePath of 'a * 'a Tree list * 'a Path * 'a Tree list

type 'a Location = Loc of 'a Tree * 'a Path

let mkTree v xs = Tree(v,xs)

let left (Loc(t, p)) = 
    match p with
    | Top -> failwith "left at top"
    | NodePath(v,l::left, up, right) -> Loc(l, NodePath(v,left, up, t::right))
    | NodePath(v,[], up, right) -> failwith "left of first"

let right (Loc(t, p)) = 
    match p with 
    | Top -> failwith "right at top"
    | NodePath(v,left, up, r::right) -> Loc(r, NodePath(v,t::left, up, right))
    | _ -> failwith "right of last"

let down (Loc(t, p)) = 
    match t with
    | Tree(_,[]) -> failwith "down with Tree"
    | Tree(v,t1::trees) -> Loc(t1, NodePath(v,[], p, trees))

let up (Loc(t,p)) = 
    match p with
    | Top -> failwith "up of top"
    | NodePath(v,left,up,right) -> 
        Loc(Tree(v, ((left |> List.rev)@[t]) @ right),up)

let rec root (Loc (t, p) as l) = 
    match p with 
    | Top -> t
    | _ -> root (up l) 

let zipper t = Loc(t, Top)

let change t (Loc(_, p)) = Loc(t, p)

let insert_right r (Loc(t, p)) = 
    match p with
    | Top -> failwith "insert at top"
    | NodePath(v,left, up, right) -> Loc(t, NodePath(v,left, up, r::right))

let insert_left l (Loc(t, p)) =
    match p with
    | Top -> failwith "insert at top"
    | NodePath(v,left, up, right) -> Loc(t, NodePath(v,l::left, up, right))

let insert_down t1 (Loc(t, p)) = 
    match t with
    | Tree (v,[]) -> Loc(t1, NodePath(v,[], p, []))
    | Tree(v,ss) -> failwith "non empty"

let delete (Loc(_, p)) =
    match p with 
    | Top -> failwith "delete at top"
    | NodePath(v,left, up, r::right) -> Loc(r, NodePath(v,left, up, right))
    | NodePath(v,l::left, up, []) -> Loc(l, NodePath(v,left, up, []))
    | NodePath(v,[], up, []) -> Loc(Tree (v,[]), up)

let rec findNodePath (x:'a) (zipper:'a Location) =
    let (Loc(Tree(value,NodePaths), path)) = zipper
    if value = x then Some zipper
    else
        match NodePaths with
        | [] -> 
            //printf " |> right "
            match path with
            | NodePath(v,left,up,[]) -> None
            | _ -> zipper |> right |> (findNodePath x)
        | _ ->
            //printf " |> down "
            let down = zipper |> down |> findNodePath x
            match down with
            | Some x -> Some x
            | None -> 
                //printfn " |> right "
                zipper |> right |> (findNodePath x)

let substs = 
    [
        "\\", "\\lambda "
        "\\lambda /","\\vee"
        "/\\lambda ","\\wedge"
        "~", "\\neg"
        "'a","\\alpha"
        "'b", "\\beta"
        "!", "\\forall "
        "==>","\\Rightarrow"
        "<=>", "\\Leftrightarrow"
        "->", "\\rightarrow"
        "|-", "\\vdash"
        " ", "\\ "
        "true", "\\top"
        "false", "\\bot"
        "?", "\\exists "
        "@", "\\epsilon "
    ]

let replace (x:string) (y:string) (s:string) = 
    s.Replace(x,y)

let strTolatex (s:string) = 
    substs
    |> List.fold 
        (
            fun acc (x,y) -> acc |> replace x y
        ) s

type Exp = 
    | Th  of thm
    | Te of term
    | Goal of (term list) * term

let rec printExp e = 
    match e with
    | Th t -> t |> print_thm |> strTolatex
    | Te t -> t |> print_term |> strTolatex
    | Goal (xs,t) -> 
        let asl = 
            xs
            |> List.map (fun t1 -> (Te t1) |> printExp)
            |> List.fold (fun acc t1 -> if acc = "" then t1 else acc + "," + t1) ""
        asl + "\\ ?\\ " + (Te t |> printExp)

let rec treeToLatex ntabs (g : Tree<Exp * string>) = 
    let tabs = "\t" |> String.replicate ntabs
    match g with
    | Tree((p,s),xs) -> 
        match xs with
        | [] -> (p |> printExp) + if s = "" then "" else "\; \mathbf{ " + s + "}"
        | _ -> 
            let prec = 
                xs
                |> List.fold (fun acc x -> (if acc = "" then "" else acc + ("\n"+ tabs + "\qquad\n" + tabs)) + (x |> treeToLatex (ntabs+1))) ""
            sprintf "\\dfrac\n%s{%s}\n%s{%s}\n%s\\textsf{ %s}" tabs prec tabs (p |> printExp) tabs s

let view proof = 
    let proofStr = proof |> treeToLatex 1
    let html = sprintf "<!DOCTYPE html><html><head><script type=\"text/javascript\" src=\"https://cdn.mathjax.org/mathjax/latest/MathJax.js\">MathJax.Hub.Config({ config: [\"TeX-AMS-MML_HTMLorMML.js\"], 	extensions: [\"[a11y]/accessibility-menu.js\"], menuSettings: {	collapsible: true,	autocollapse: true,	explorer: true } });</script></head><body>\\[ \\small{ 	%s } \\]</body></html>" proofStr
    let path = System.IO.Path.GetTempFileName() + ".html"
    let mutable file = File.CreateText(path)
    file.WriteLine(html)
    file.Flush()
    System.Diagnostics.Process.Start(@"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",path)

let print_tree (t,g) = 
    g |> view |> ignore
    t |> print_thm

(* Rules *)

let assume_rule_tr t = 
    let th = t |> assume_rule
    (th, mkTree (Th th,"assume_rule") [mkTree (Te t,"") []])

let eta_conv_tr t = 
    let th = t |> eta_conv
    (th, mkTree (Th th,"eta_conv") [mkTree (Te t,"") []])

let refl_conv_tr t = 
    let th = t |> refl_conv
    (th, mkTree (Th th,"refl_conv") [mkTree (Te t,"") []])

let sym_rule_tr (th1,g1) = 
    let th = th1 |> sym_rule
    (th, mkTree (Th th,"sym_rule") [g1])

let spec_rule_tr t (th1,g1) = 
    let th = th1 |> spec_rule t
    (th, mkTree (Th th,"spec_rule") [mkTree (Te t,"") [];g1])

let mk_abs_rule_tr t (th1,g1) = 
    let th = th1 |> mk_abs_rule t
    (th, mkTree (Th th,"mk_abs_rule") [mkTree (Te t,"") [];g1])

let list_trans_rule_tr xs = 
    let thms = xs |> List.map (fun (th,_) -> th)
    let gs = xs |> List.map (fun (_,g) -> g)
    let th = thms |> list_trans_rule 
    (th, mkTree (Th th,"list_trans_rule") gs)

let mk_comb1_rule_tr (th1,g1) t = 
    let th = mk_comb1_rule th1 t
    (th, mkTree (Th th,"mk_comb1_rule") [g1;mkTree (Te t,"") []])

let disj1_rule_tr (th1,g1) t = 
    let th = disj1_rule th1 t
    (th, mkTree (Th th,"disj1_rule") [g1;mkTree (Te t,"") []])

let gen_rule_tr t (th1,g1) = 
    let th = th1 |> gen_rule t
    (th, mkTree (Th th,"gen_rule") [mkTree (Te t,"") [];g1])

let deduct_antisym_rule_tr (th1,g1) (th2,g2) = 
    let th = deduct_antisym_rule th1 th2
    (th, mkTree (Th th,"deduct_antisym_rule") [g1;g2])

let list_gen_rule_tr xs (th1,g1) = 
    let trms = xs |> List.map (fun t -> mkTree (Te t,"") [])
    let th = list_gen_rule xs th1
    (th, mkTree (Th th,"list_gen_rule") (trms@[g1]))

let eq_mp_rule_tr (th1,g1) (th2,g2) = 
    let th = eq_mp_rule th1 th2
    (th, mkTree (Th th,"eq_mp_rule") [g1;g2])

let exists_rule_tr (t1,t2) (th1,g1) = 
    let th = th1 |> exists_rule (t1,t2)
    (th, mkTree (Th th,"exists_rule") [mkTree (Te t1,"") [];mkTree (Te t2,"") [];g1])

let select_rule_tr (th1,g1) = 
    let th = th1 |> select_rule
    (th, mkTree (Th th,"select_rule") [g1])

let mk_eq_rule_tr (th1,g1) (th2,g2) = 
    let th = mk_eq_rule th1 th2
    (th, mkTree (Th th,"mk_eq_rule") [g1;g2])

let disj2_rule_tr t (th1,g1) = 
    let th = th1 |> disj2_rule t
    (th, mkTree (Th th,"disj2_rule") [mkTree (Te t,"") [];g1])

let mk_select_rule_tr t (th1,g1) = 
    let th = th1 |> mk_select_rule t
    (th, mkTree (Th th,"mk_select_rule") [mkTree (Te t,"") [];g1])

let disch_rule_tr t (th1,g1) = 
    let th = th1 |> disch_rule t
    (th, mkTree (Th th,"disch_rule") [mkTree (Te t,"") [];g1])

let not_intro_rule_tr (th1,g1) = 
    let th = th1 |> not_intro_rule
    (th, mkTree (Th th,"not_intro_rule") [g1])

let disj_cases_rule_tr (th1,g1) (th2,g2) (th3,g3) = 
    let th = disj_cases_rule th1 th2 th3
    (th, mkTree (Th th,"disj_cases_rule") [g1;g2;g3])

let eqt_intro_rule_tr (th1,g1) = 
    let th = th1 |> eqt_intro_rule
    (th, mkTree (Th th,"eqt_intro_rule") [g1])

let eqf_intro_rule_tr (th1,g1) = 
    let th = th1 |> eqf_intro_rule
    (th, mkTree (Th th,"eqf_intro_rule") [g1])

let contr_rule_tr t (th1,g1) = 
    let th = th1 |> contr_rule t
    (th, mkTree (Th th,"contr_rule") [mkTree (Te t,"") [];g1])

let eqf_elim_rule_tr (th1,g1) = 
    let th = th1 |> eqf_elim_rule
    (th, mkTree (Th th,"eqf_elim_rule") [g1])

let undisch_rule_tr (th1,g1) = 
    let th = th1 |> undisch_rule
    (th, mkTree (Th th,"undisch_rule") [g1])

let conjunct1_rule_tr (th1,g1) = 
    let th = th1 |> conjunct1_rule
    (th, mkTree (Th th,"conjunct1_rule") [g1])

let conjunct2_rule_tr (th1,g1) = 
    let th = th1 |> conjunct2_rule
    (th, mkTree (Th th,"conjunct2_rule") [g1])

let conj_rule_tr (th1,g1) (th2,g2) = 
    let th = conj_rule th1 th2
    (th, mkTree (Th th,"conj_rule") [g1;g2])

let deduct_contrapos_rule_tr t (th1,g1) = 
    let th = th1 |> deduct_contrapos_rule t
    (th, mkTree (Th th,"deduct_contrapos_rule") [mkTree (Te t,"") [];g1])

let not_elim_rule_tr (th1,g1) = 
    let th = th1 |> not_elim_rule
    (th, mkTree (Th th,"not_elim_rule") [g1])
[<AutoOpen>]
module HOL.ProofUtils

open System.IO

/// proof tree
type Graph<'a> = 
    | Graph of 'a * 'a Graph List
    member x.children = let (Graph(_, xs)) = x in xs
    member x.value = let (Graph(v, _)) = x in v
    override x.ToString() = 
        match x with
        | Graph(v,[]) -> v.ToString()
        | Graph(v,xs) -> sprintf "(%O,%O)" v xs

let mkGraph v xs = Graph(v,xs)

let substs = 
    [
        "\\", "\\lambda "
        "\\lambda /","\\vee"
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

let printExp e = 
    match e with
    | Th t -> t |> print_thm |> strTolatex
    | Te t -> t |> print_term |> strTolatex

let rec graphToLatex ntabs (g : Graph<Exp * string>) = 
    let tabs = "\t" |> String.replicate ntabs
    match g with
    | Graph((p,s),xs) -> 
        match xs with
        | [] -> (p |> printExp) + if s = "" then "" else "\; \mathbf{ " + s + "}"
        | _ -> 
            let prec = 
                xs
                |> List.fold (fun acc x -> (if acc = "" then "" else acc + ("\n"+ tabs + "\qquad\n" + tabs)) + (x |> graphToLatex (ntabs+1))) ""
            sprintf "\\dfrac\n%s{%s}\n%s{%s}\n%s\\textsf{ %s}" tabs prec tabs (p |> printExp) tabs s

let view proof = 
    let proofStr = proof |> graphToLatex 1
    let html = sprintf "<!DOCTYPE html><html><head><script type=\"text/javascript\" src=\"https://cdn.mathjax.org/mathjax/latest/MathJax.js\">MathJax.Hub.Config({ config: [\"TeX-AMS-MML_HTMLorMML.js\"], 	extensions: [\"[a11y]/accessibility-menu.js\"], menuSettings: {	collapsible: true,	autocollapse: true,	explorer: true } });</script></head><body>\\[ \\small{ 	%s } \\]</body></html>" proofStr
    let path = System.IO.Path.GetTempFileName() + ".html"
    let mutable file = File.CreateText(path)
    file.WriteLine(html)
    file.Flush()
    System.Diagnostics.Process.Start(@"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",path)

let print_graph (t,g) = 
    g |> view |> ignore
    t |> print_thm

(* Rules *)

let assume_rule_tr t = 
    let th = t |> assume_rule
    (th, mkGraph (Th th,"assume_rule") [mkGraph (Te t,"") []])

let eta_conv_tr t = 
    let th = t |> eta_conv
    (th, mkGraph (Th th,"eta_conv") [mkGraph (Te t,"") []])

let refl_conv_tr t = 
    let th = t |> refl_conv
    (th, mkGraph (Th th,"refl_conv") [mkGraph (Te t,"") []])

let sym_rule_tr (th1,g1) = 
    let th = th1 |> sym_rule
    (th, mkGraph (Th th,"sym_rule") [g1])

let spec_rule_tr t (th1,g1) = 
    let th = th1 |> spec_rule t
    (th, mkGraph (Th th,"spec_rule") [mkGraph (Te t,"") [];g1])

let mk_abs_rule_tr t (th1,g1) = 
    let th = th1 |> mk_abs_rule t
    (th, mkGraph (Th th,"mk_abs_rule") [mkGraph (Te t,"") [];g1])

let list_trans_rule_tr xs = 
    let thms = xs |> List.map (fun (th,_) -> th)
    let gs = xs |> List.map (fun (_,g) -> g)
    let th = thms |> list_trans_rule 
    (th, mkGraph (Th th,"list_trans_rule") gs)

let mk_comb1_rule_tr (th1,g1) t = 
    let th = mk_comb1_rule th1 t
    (th, mkGraph (Th th,"mk_comb1_rule") [g1;mkGraph (Te t,"") []])

let disj1_rule_tr (th1,g1) t = 
    let th = disj1_rule th1 t
    (th, mkGraph (Th th,"disj1_rule") [g1;mkGraph (Te t,"") []])

let gen_rule_tr t (th1,g1) = 
    let th = th1 |> gen_rule t
    (th, mkGraph (Th th,"gen_rule") [mkGraph (Te t,"") [];g1])

let deduct_antisym_rule_tr (th1,g1) (th2,g2) = 
    let th = deduct_antisym_rule th1 th2
    (th, mkGraph (Th th,"deduct_antisym_rule") [g1;g2])

let list_gen_rule_tr xs (th1,g1) = 
    let trms = xs |> List.map (fun t -> mkGraph (Te t,"") [])
    let th = list_gen_rule xs th1
    (th, mkGraph (Th th,"list_gen_rule") (trms@[g1]))

let eq_mp_rule_tr (th1,g1) (th2,g2) = 
    let th = eq_mp_rule th1 th2
    (th, mkGraph (Th th,"eq_mp_rule") [g1;g2])

let exists_rule_tr (t1,t2) (th1,g1) = 
    let th = th1 |> exists_rule (t1,t2)
    (th, mkGraph (Th th,"exists_rule") [mkGraph (Te t1,"") [];mkGraph (Te t2,"") [];g1])

let select_rule_tr (th1,g1) = 
    let th = th1 |> select_rule
    (th, mkGraph (Th th,"select_rule") [g1])

let mk_eq_rule_tr (th1,g1) (th2,g2) = 
    let th = mk_eq_rule th1 th2
    (th, mkGraph (Th th,"mk_eq_rule") [g1;g2])

let disj2_rule_tr t (th1,g1) = 
    let th = th1 |> disj2_rule t
    (th, mkGraph (Th th,"disj2_rule") [mkGraph (Te t,"") [];g1])

let mk_select_rule_tr t (th1,g1) = 
    let th = th1 |> mk_select_rule t
    (th, mkGraph (Th th,"mk_select_rule") [mkGraph (Te t,"") [];g1])

let disch_rule_tr t (th1,g1) = 
    let th = th1 |> disch_rule t
    (th, mkGraph (Th th,"disch_rule") [mkGraph (Te t,"") [];g1])

let not_intro_rule_tr (th1,g1) = 
    let th = th1 |> not_intro_rule
    (th, mkGraph (Th th,"not_intro_rule") [g1])

let disj_cases_rule_tr (th1,g1) (th2,g2) (th3,g3) = 
    let th = disj_cases_rule th1 th2 th3
    (th, mkGraph (Th th,"disj_cases_rule") [g1;g2;g3])

let eqt_intro_rule_tr (th1,g1) = 
    let th = th1 |> eqt_intro_rule
    (th, mkGraph (Th th,"eqt_intro_rule") [g1])

let eqf_intro_rule_tr (th1,g1) = 
    let th = th1 |> eqf_intro_rule
    (th, mkGraph (Th th,"eqf_intro_rule") [g1])
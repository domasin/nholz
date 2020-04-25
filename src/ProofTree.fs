[<AutoOpen>]
module HOL.ProofTree

type Exp = 
    | NullExp
    | Th  of thm
    | Te of term
    | Tye of hol_type
    | TeLst of term list
    | InstTyLst of (hol_type * hol_type) list
    | InstTmLst of (term * term) list
    | Goal of (term list) * term

type InfRule = 
    | NullFun
    | TmFn of (term -> thm)
    | ThmFn of (thm -> thm)
    | ThmThmFn of (thm -> thm -> thm)
    | ThmThmThmFn of (thm -> thm -> thm -> thm)
    | TmThmFn of (term -> thm -> thm)
    | TmThmThmFn of (term -> thm -> thm -> thm)
    | ThmTmFn of (thm -> term -> thm)
    | TmLstThmFn of (term list -> thm -> thm)
    | ThmLstFn of (thm list -> thm)
    | InstTyLstThmFn of ((hol_type * hol_type) list -> thm -> thm)
    | InstTmLstThmFn of ((term * term) list -> thm -> thm)

type Proof = (Exp * string * InfRule)
type goal = (term list) * term

let exp (loc:Proof Location) = 
    match loc with
    | Loc(Tree((e,_,_),_), _) -> e

let is_goal (exp:Exp) = 
    match exp with
    | Goal (_,_) -> true
    | _ -> false

let loc_thm (loc:Proof Location) = 
    match loc with
    | Loc(Tree((Th t,_,_),_), _) -> Some t
    | _ -> None

let loc_term (loc:Proof Location) = 
    match loc with
    | Loc(Tree((Te t,_,_),_), _) -> Some t
    | _ -> None

let loc_goal (loc:Proof Location) = 
    match loc with
    | Loc(Tree((Goal (asl,t),_,_),_), _) -> Some (Goal (asl,t))
    | _ -> None

let lower : (Proof Location -> Proof Location) = up

// printing

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

let rec printExp e = 
    match e with
    | Th t -> t |> print_thm |> strTolatex
    | Te t -> t |> print_term |> strTolatex
    | Tye t -> t |> print_type |> strTolatex
    | Goal (xs,t) -> 
        let asl = 
            xs
            |> List.map (fun t1 -> (Te t1) |> printExp)
            |> List.fold (fun acc t1 -> if acc = "" then t1 else acc + "," + t1) ""
        asl + "\\ ?\\ " + (Te t |> printExp)
    | TeLst vv -> 
        let lstStr = 
            vv |> List.map (fun x -> (Te x) |> printExp)
            |> List.fold (fun acc t1 -> if acc = "" then t1 else acc + ";" + t1) ""
        "[" + lstStr + "]"
    | InstTyLst vv -> 
        let lstStr = 
            vv |> List.map (fun (x,y) -> "(" + ((Tye x) |> printExp) + "," + ((Tye y) |> printExp) + ")")
            |> List.fold (fun acc t1 -> if acc = "" then t1 else acc + ";" + t1) ""
        "[" + lstStr + "]"
    | InstTmLst vv -> 
        let lstStr = 
            vv |> List.map (fun (x,y) -> "(" + ((Te x) |> printExp) + "," + ((Te y) |> printExp) + ")")
            |> List.fold (fun acc t1 -> if acc = "" then t1 else acc + ";" + t1) ""
        "[" + lstStr + "]"
    | NullExp -> ""

let rec treeToLatex ntabs exp (tr : Proof Tree) = 
    let tabs = "\t" |> String.replicate ntabs
    match tr with
    | Tree((p,s,_),xs) -> 
        match xs with
        | [] -> 
            let expStr = if p = exp && (exp |> is_goal) then "\color{red}{" + (p |> printExp)  + "}" else (p |> printExp) 
            expStr + if s = "" then "" else "\; \mathbf{ " + s + "}"
        | _ -> 
            let prec = 
                xs
                |> List.fold 
                    (
                        fun acc x -> 
                            (
                                if acc = "" then "" 
                                else acc + ("\n"+ tabs + "\qquad\n" + tabs)) + (x |> treeToLatex (ntabs+1) exp)) ""
            match p with
            | Th _ -> 
                sprintf "\\color{green}{\\dfrac\n%s{%s}\n%s{%s}\n%s\\textsf{ %s}}" tabs prec tabs (p |> printExp) tabs s
            | _ -> 
                sprintf "\\dfrac\n%s{%s}\n%s{%s}\n%s\\textsf{ %s}" tabs prec tabs (if p = exp && (exp |> is_goal) then "\color{red}{" + (p |> printExp)  + "}" else (p |> printExp) ) tabs s

open System.IO

let view (loc:Proof Location) =
    let (Loc(Tree((exp,_,_),_), _)) = loc
    let proof = loc |> root
    let proofStr = proof |> treeToLatex 1 exp
    let html = sprintf "<!DOCTYPE html><html><head><script type=\"text/javascript\" src=\"https://cdn.mathjax.org/mathjax/latest/MathJax.js\">MathJax.Hub.Config({ config: [\"TeX-AMS-MML_HTMLorMML.js\"], 	extensions: [\"[a11y]/accessibility-menu.js\"], menuSettings: {	collapsible: true,	autocollapse: true,	explorer: false } });</script></head><body>\\[ \\small{ 	%s } \\]</body></html>" proofStr
    let path = System.IO.Path.GetTempFileName() + ".html"
    let mutable file = File.CreateText(path)
    file.WriteLine(html)
    file.Flush()
    System.Diagnostics.Process.Start(@"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",path) |> ignore
    loc

let linearizeProof (tr: Proof Tree) = 

    let listToString xs = 
        match xs with
        | [] -> ""
        | _ -> xs |> List.fold (fun acc x -> if acc = "" then x.ToString()  else acc + "," + x.ToString()) ""

    let rec treeToList acc (tr: Proof Tree) = 
        match tr with
        | Tree(x,[]) -> 
            match x with
            | (Th _,_,_) -> 
                acc@[x,[]]
            | _ -> acc
        | Tree(x,xs) -> 
            xs
            |> List.map (fun x -> x |> treeToList acc)
            |> List.concat
            |> fun lst -> lst@[x,xs |> List.map (fun (Tree(e,_)) -> e)]

    let remapChild (xs:(Proof * Proof list) list) = 
        let indexed = 
            xs 
            |> List.mapi (fun i x -> (i,x))
        indexed 
        |> List.map (fun (i,((e,l,f),cs)) -> (i,((e,l,f),cs |> List.map (fun (c,_,_) -> 
                        indexed 
                        |> List.filter (fun (i',((e',_,_),_)) -> e' = c && i' < i) 
                        |> List.map (fun (i',(_,_)) -> i') 
                        |> List.rev |> fun x -> if x = [] then 9999999 else (x |> List.head)) |> List.filter (fun x -> x <> 9999999))))
    tr
    |> treeToList []
    |> remapChild
    |> List.iter 
        (
            fun p -> 
                match p with
                | (i,((Th t,lbl,_),childs)) -> 
                    let (asms,concl) = dest_thm t
                    let asmStr = asms |> List.fold (fun acc x -> if acc = "" then x |> print_term else acc + ", " + (x |> print_term) ) ""
                    let conclStr = concl |> print_term
                    printfn "%-5i %30s |- %-50s %-25s %-10s" i asmStr conclStr lbl (childs |> listToString)
                | _ -> ()
        )
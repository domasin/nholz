module HOL.PropUtils

let (|False|_|) tm =
   match tm with
   | Tmconst ("false", Tycomp ("bool", [])) -> Some false_tm
   | _ -> None 

let (|True|_|) tm =
   match tm with
   | Tmconst ("true", Tycomp ("bool", [])) -> Some true_tm
   | _ -> None

let (|Atom|_|) tm =
   match tm with
   | Tmvar (p, Tycomp ("bool", [])) -> Some p
   | _ -> None

let (|Not|_|) tm =
   match tm with
   | Tmcomb (Tmconst ("~", Tycomp ("->", [Tycomp ("bool", []); Tycomp ("bool", [])])), p) -> Some p
   | _ -> None

let (|And|_|) tm =
   match tm with
   | Tmcomb (Tmcomb (Tmconst ("/\\", Tycomp ("->", [Tycomp ("bool", []); Tycomp ("->", [Tycomp ("bool", []); Tycomp ("bool", [])])])), p), q) -> 
        Some (p,q)
   | _ -> None
let (|Or|_|) tm =
   match tm with
   | Tmcomb (Tmcomb (Tmconst ("\\/", Tycomp ("->", [Tycomp ("bool", []); Tycomp ("->", [Tycomp ("bool", []); Tycomp ("bool", [])])])), p), q) -> 
        Some (p,q)
   | _ -> None

let (|Imp|_|) tm =
   match tm with
   | Tmcomb (Tmcomb (Tmconst ("==>", Tycomp ("->", [Tycomp ("bool", []); Tycomp ("->", [Tycomp ("bool", []); Tycomp ("bool", [])])])), p), q)-> 
        Some (p,q)
   | _ -> None

let (|Iff|_|) tm =
   match tm with
   | Tmcomb (Tmcomb (Tmconst ("=", Tycomp ("->", [Tycomp ("bool", []); Tycomp ("->", [Tycomp ("bool", []); Tycomp ("bool", [])])])), p), q)-> 
        Some (p,q)
   | _ -> None

/// returns constant or variable name of a term
let pname tm = 
    if tm |> is_const then 
        tm |> const_name
    elif tm |> is_var then 
        tm |> var_name
    else ""

let rec eval v tm =
    match tm with
    | False _ -> false
    | True _ -> true
    | Atom _ -> v tm
    | Not p -> not <| eval v p
    | And (p, q) -> (eval v p) && (eval v q)
    | Or (p, q) -> (eval v p) || (eval v q)
    | Imp (p, q) -> not(eval v p) || (eval v q)
    | Iff (p, q) -> (eval v p) = (eval v q)
    | _ -> failwith "Not part of propositional logic."

/// the term is a boolean atom
let is_bool_atom tm = 
    tm |> is_bool_term && (tm |> is_const || tm |> is_var)

let rec overatoms f tm b =
    if tm |> is_bool_atom then 
        f tm b
    elif tm |> is_not then
        let p = tm |> dest_not
        overatoms f p b
    elif tm |> is_conj then
        let (p,q) = tm |> dest_conj
        overatoms f p (overatoms f q b)
    elif tm |> is_disj then
        let (p,q) = tm |> dest_disj
        overatoms f p (overatoms f q b)
    elif tm |> is_imp then
        let (p,q) = tm |> dest_imp
        overatoms f p (overatoms f q b)
    elif tm |> is_eq then
        let (p,q) = tm |> dest_eq
        overatoms f p (overatoms f q b)
    else failwith "check type annotation on eq"

let atom_union f tm =
    (tm, [])
    ||> overatoms (fun h (t) -> (f h) @ t)
    |> setify

let atoms tm = 
    atom_union (fun a -> [a]) tm

// let rec eval v tm =
//     if tm = false_tm then 
//         false
//     elif tm = true_tm then
//         true
//     elif tm |> is_bool_atom then 
//         v tm
//     elif tm |> is_not then 
//         let p = tm |> dest_not
//         not <| eval v p
//     elif tm |> is_conj then 
//         let (p,q) = tm |> dest_conj
//         (eval v p) && (eval v q)
//     elif tm |> is_disj then 
//         let (p,q) = tm |> dest_disj
//         (eval v p) || (eval v q)
//     elif tm |> is_imp then 
//         let (p,q) = tm |> dest_imp
//         not(eval v p) || (eval v q)
//     elif tm |> is_eq then 
//         let (p,q) = tm |> dest_eq
//         (eval v p) = (eval v q)
//     else
//         failwith "Not part of propositional logic."

let rec onallvaluations subfn v ats =
    match ats with
    | [] -> subfn v
    | p :: ps ->
        let v' t q =
            if q = p then t
            else v q
        onallvaluations subfn (v' false) ps
        && onallvaluations subfn (v' true) ps

let fprint_truthtable sw fm =
    // [P "p"; P "q"; P "r"]
    let ats = atoms fm
    // 5 + 1 = length of false + length of space
    let width = List.foldBack (max << String.length << pname) ats 5 + 1
    let fixw s = s + String.replicate (width - String.length s) " "
    let truthstring p = fixw (if p then "true" else "false")
    let mk_row v =
        let lis = ats |> map (fun x -> 
            match x with
            | Tmconst ("true", Tycomp ("bool", [])) -> fixw "true"
            | Tmconst ("false", Tycomp ("bool", [])) -> fixw "false"
            | _ -> truthstring(v x)
            )
        let ans = truthstring (eval v fm)
        fprintf sw "%s" (List.foldBack (+) lis ("| " + ans))
        fprintfn sw ""
        true
    let seperator = String.replicate (width * (List.length ats) + 9) "-"
    fprintfn sw "%s" (List.foldBack (fun s t -> fixw(pname s) + t) ats "| formula")
    fprintfn sw "%s" seperator
    let _ = onallvaluations mk_row (fun x -> false) ats
    fprintfn sw "%s" seperator
    fprintfn sw ""

let writeToString fn = 
    use sw = new System.IO.StringWriter()
    fn sw
    sw.ToString()

let inline print_truthtable f = fprint_truthtable stdout f
let inline sprint_truthtable f = writeToString (fun sw -> fprint_truthtable sw f)

/// checks if a term in the propositional fragment is a tautology
let tautology tm =
    onallvaluations (fun v -> tm |> eval v) (fun s -> false) (atoms tm)

/// checks if a term in the propositional fragment is unsatisfiable
let unsatisfiable fm = 
    fm |> mk_not |> tautology

/// checks if a term in the propositional fragment is satisfiable
let satisfiable fm = 
    not <| unsatisfiable fm

/// returns the dual of a term in the propositional fragment
let rec dual tm =
    match tm with
    | False _ -> true_tm
    | True _ -> false_tm
    | Atom _-> tm
    | Not p -> p |> dual |> mk_not
    | And (p,q)-> 
        mk_disj (dual p, dual q)
    | Or (p,q) -> 
        mk_conj (dual p, dual q)
    | _ ->
        failwith "Formula involves connectives ==> or <=>"

/// auxiliary function for psimplify
let psimplify1 tm =
   match tm with
   | Not f when f = false_tm -> true_tm
   | Not t when t = true_tm -> false_tm
   | Not(Not p) -> p
   | And(p,f) when f = false_tm -> false_tm
   | And(f,p) when f = false_tm -> false_tm
   | And(p,t) when t = true_tm -> p 
   | And(t,p) when t = true_tm -> p 
   | Or(p,f) when f = false_tm -> p
   | Or(f,p) when f = false_tm -> p
   | Or(p,t) when t = true_tm -> true_tm
   | Or(t,p) when t = true_tm -> true_tm
   | Imp(f,p) when f = false_tm -> true_tm
   | Imp(p,t) when t = true_tm -> true_tm
   | Imp(t,p) when t = true_tm -> p
   | Imp(p,f) when f = false_tm -> p |> mk_not
   | Iff(p,t) when t = true_tm -> p
   | Iff(t,p) when t = true_tm -> p
   | Iff(p,f) when f = false_tm -> p |> mk_not
   | Iff(f,p) when f = false_tm -> p |> mk_not
   | _ -> tm;;
        
/// simplifies a boolean term removing the base constants true and false
let rec psimplify fm =
    match fm with
    | Not p ->
        psimplify1 (mk_not (psimplify p))
    | And (p, q) ->
        psimplify1 (mk_conj (psimplify p, psimplify q))
    | Or (p, q) ->
        psimplify1 (mk_disj (psimplify p, psimplify q))
    | Imp (p, q) ->
        psimplify1 (mk_imp (psimplify p, psimplify q))
    | Iff (p, q) ->
        psimplify1 (mk_eq (psimplify p, psimplify q))
    | fm -> fm

// ------------------------------------------------------------------------- //
// Some operations on literals.                                              //
// ------------------------------------------------------------------------- //

/// checks if a litteral is negative
let negative = function
    | Not p -> true
    | _ -> false
    
/// checks if a litteral is positive
let positive lit = not <| negative lit
    
/// change a litteral into its contrary
let negate = function
    | Not p -> p
    | p -> p |> mk_not

// ------------------------------------------------------------------------- //
// Negation normal form.                                                     //
// ------------------------------------------------------------------------- //

/// cahnge a formula into its negation normal form 
/// without simplifying it
let rec nnfOrig fm =
    match fm with
    | And (p, q) ->
        mk_conj (nnfOrig p, nnfOrig q)
    | Or (p, q) ->
        mk_disj (nnfOrig p, nnfOrig q)
    | Imp (p, q) ->
        mk_disj (nnfOrig (mk_not p), nnfOrig q)
    | Iff (p, q) ->
        mk_disj (mk_conj (nnfOrig p, nnfOrig q),
            mk_conj (nnfOrig (mk_not p), nnfOrig (mk_not q)))
    | Not (Not p) ->
        nnfOrig p
    | Not (And (p, q)) ->
        mk_disj (nnfOrig (mk_not p), nnfOrig (mk_not q))
    | Not (Or (p, q)) ->
        mk_conj (nnfOrig (mk_not p), nnfOrig (mk_not q))
    | Not (Imp (p, q)) ->
        mk_conj (nnfOrig p, nnfOrig (mk_not q))
    | Not (Iff (p, q)) ->
        mk_disj (mk_conj (nnfOrig p, nnfOrig (mk_not q)),
            mk_conj (nnfOrig (mk_not p), nnfOrig q))
    | fm -> fm

/// cahnge a formula into its negation normal form and simplifies it
let nnf fm =
    nnfOrig <| psimplify fm

// ------------------------------------------------------------------------- //
// Simple negation-pushing when we don't care to distinguish occurrences.    //
// ------------------------------------------------------------------------- //

/// auxiliary function to define nenf
let rec nenfOrig fm =
    match fm with
    | Not (Not p) ->
        nenfOrig p
    | Not (And (p, q)) ->
        mk_disj (nenfOrig (mk_not p), nenfOrig (mk_not q))
    | Not (Or (p, q)) ->
        mk_conj (nenfOrig (mk_not p), nenfOrig (mk_not q))
    | Not (Imp (p, q)) ->
        mk_conj (nenfOrig p, nenfOrig (mk_not q))
    | Not (Iff (p, q)) ->
        mk_imp (nenfOrig p, nenfOrig (mk_not q))
    | And (p, q) ->
        mk_conj (nenfOrig p, nenfOrig q)
    | Or (p, q) ->
        mk_disj (nenfOrig p, nenfOrig q)
    | Imp (p, q) ->
        mk_disj (nenfOrig (mk_not p), nenfOrig q)
    | Iff (p, q) ->
        mk_eq (nenfOrig p, nenfOrig q)
    | fm -> fm

/// a version of nnf that don't transform iif
let nenf fm =
    nenfOrig <| psimplify fm
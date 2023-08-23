/// Functions to automate tautology and satisfiability in the propositional 
/// fragment.
/// 
/// The module implements ideas described in the book "handbook of practical
/// logic and automated reasoning" (https://www.cl.cam.ac.uk/~jrh13/atp/)
/// adapting the code to fit nholz HOL system.
/// 
/// Many of the implementations are based on the version of the code ported in 
/// F# by https://github.com/jack-pappas/fsharp-logic-examples/.
[<AutoOpen>]
module HOL.AutomatedReasoning.PropUtils

open HOL

/// returns constant or variable name of a propositional term
let pname tm = 
    if tm |> is_const then 
        tm |> const_name
    elif tm |> is_var then 
        tm |> var_name
    else ""

/// Interpretation of propositional terms
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

/// Return the set of propositional terms in a formula
let atoms tm = 
    atom_union (fun a -> [a]) tm

// ------------------------------------------------------------------------- //
// Code to print out truth tables.                                           //
// ------------------------------------------------------------------------- //

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

// ------------------------------------------------------------------------- //
// Recognizing validity and satisfiability.                                  //
// ------------------------------------------------------------------------- //

/// checks if a propositional term is a tautology
let tautology tm =
    onallvaluations (fun v -> tm |> eval v) (fun s -> false) (atoms tm)

/// checks if a term in the propositional fragment is unsatisfiable
let unsatisfiable fm = 
    fm |> mk_not |> tautology

/// checks if a term in the propositional fragment is satisfiable
let satisfiable fm = 
    not <| unsatisfiable fm

// ------------------------------------------------------------------------- //
// Dualization.                                                              //
// ------------------------------------------------------------------------- //

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

// ------------------------------------------------------------------------- //
// Routine simplification.                                                   //
// ------------------------------------------------------------------------- //

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

// ------------------------------------------------------------------------- //
// Roll in simplification.                                                   //
// ------------------------------------------------------------------------- //

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

// ------------------------------------------------------------------------- //
// Disjunctive normal form (DNF) via truth tables.                           //
// ------------------------------------------------------------------------- //

let list_conj l =
    if l = [] then true_tm
    else list_mk_conj l

let list_disj l = 
    if l = [] then false_tm 
    else list_mk_disj l

let mk_lits pvs v =
    list_conj (map (fun p -> if eval v p then p else mk_not p) pvs)

let rec allsatvaluations subfn v pvs =
    match pvs with
    | [] ->
        if subfn v then [v] else []
    | p :: ps -> 
        let v' t q =
            if q = p then t
            else v q
        allsatvaluations subfn (v' false) ps @
        allsatvaluations subfn (v' true) ps

let dnfOrig fm =
    let pvs = atoms fm
    let satvals = allsatvaluations (fun v -> eval v fm) (fun s -> false) pvs
    list_disj (List.map (mk_lits (List.map (id) pvs)) satvals)

// ------------------------------------------------------------------------- //
// DNF via distribution.                                                     //
// ------------------------------------------------------------------------- //

let rec distribOrig fm =
    match fm with
    | And (p, Or (q, r)) ->
        mk_disj (distribOrig (mk_conj (p, q)), distribOrig (mk_conj (p, r)))
    | And (Or (p, q), r) ->
        mk_disj (distribOrig (mk_conj (p, r)), distribOrig (mk_conj (q, r)))
    | _ -> fm

let rec rawdnf fm =
    match fm with
    | And (p, q) ->
        distribOrig <| mk_conj (rawdnf p, rawdnf q)
    | Or (p, q) ->
        mk_disj (rawdnf p, rawdnf q)
    | _ -> fm

// ------------------------------------------------------------------------- //
// A dnf version using a list representation.                                //
// ------------------------------------------------------------------------- //

let distrib s1 s2 =
    setify <| allpairs union s1 s2

let rec purednf fm =
    match fm with
    | And (p, q) ->
        distrib (purednf p) (purednf q)
    | Or (p, q) ->
        union (purednf p) (purednf q)
    | _ -> [[fm]]

// ------------------------------------------------------------------------- //
// Filtering out trivial disjuncts (in this guise, contradictory).           //
// ------------------------------------------------------------------------- //

let trivial lits =
    let pos, neg = List.partition positive lits
    intersect pos (image negate neg) <> []

// ------------------------------------------------------------------------- //
// With subsumption checking, done very naively (quadratic).                 //
// ------------------------------------------------------------------------- //

let simpdnf fm =
    if fm = false_tm then [] 
    elif fm = true_tm then [[]] 
    else
        let djs = List.filter (not << trivial) (purednf (nnf fm))
        List.filter (fun d -> not (List.exists (fun d' -> psubset d' d) djs)) djs

// ------------------------------------------------------------------------- //
// Mapping back to a formula.                                                //
// ------------------------------------------------------------------------- //

/// Disjuntive normal form
let dnf fm =
    List.map list_conj (simpdnf fm)
    |> list_disj

// ------------------------------------------------------------------------- //
// Conjunctive normal form (CNF) by essentially the same code.               //
// ------------------------------------------------------------------------- //

let purecnf fm = image (image negate) (purednf (nnf (mk_not fm)))

let simpcnf fm =
    if fm = false_tm then [[]]
    elif fm = true_tm then []
    else
        let cjs = List.filter (not << trivial) (purecnf fm)
        List.filter (fun c -> not (List.exists (fun c' -> psubset c' c) cjs)) cjs

/// conjuctive normal form
let cnf fm =
    List.map list_disj (simpcnf fm)
    |> list_conj
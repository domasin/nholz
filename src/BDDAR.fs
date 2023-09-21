/// Binary decision diagrams (BDDs) using complement edges. 
/// 
/// The module is the porting of the union-find algorithm defined in the file 
/// bdd.ml from the code that accompanies the book "handbook of practical 
/// logic and automated reasoning" (https://www.cl.cam.ac.uk/~jrh13/atp/) 
/// adapted to fit nholz HOL system.
/// 
/// Many of the implementations are based on the version of the code ported in 
/// F# by https://github.com/jack-pappas/fsharp-logic-examples/.
[<AutoOpen>]
module HOL.AutomatedReasoning.BDD

open HOL

// ========================================================================= //
// Binary decision diagrams (BDDs) using complement edges.                   //
//                                                                           //
// In practice one would use hash tables, but we use abstract finite         //
// partial functions here. They might also look nicer imperatively.          //
// ========================================================================= //


type bddnode = 
    // propositional variable, left node, right node
    string * int * int

/// A Binary Decision Diagram
type bdd = 
    Bdd of 
        (
            func<bddnode, int>        // unique table
            * func<int, bddnode>      // expansion table
            * int                     // smallest positive unused node index
        )   
        *  (string -> string -> bool) // variable order

let print_bdd (Bdd ((unique, uback, n), ord)) =
    printf "<BDD with %i nodes>" n

let emptyTerm = Tmvar ("", Tycomp ("bool", []))

/// Returns the bddnode corresponding to the index `n` of the bdd
/// If a negative index is used the complement of the node is returned.
let expand_node (Bdd ((_, expand, _), _)) n =
    if n >= 0 then
        tryapplyd expand n ("", 1, 1)
    else 
        let p, l, r = tryapplyd expand -n ("", 1, 1)
        p, -l, -r

/// Lookup or insertion if not there in unique table. 
let lookup_unique (Bdd ((unique, expand, n), ord) as bdd) node =
    try bdd, apply unique node
    with _ ->
        Bdd (((node |-> n) unique, (n |-> node) expand, n + 1), ord), n

/// Produce a BDD node (old or new).
let mk_node bdd (s, l, r) =
    if l = r then bdd, l
    elif l >= 0 then
        lookup_unique bdd (s, l, r)
    else 
        let bdd', n = lookup_unique bdd (s, -l, -r) 
        bdd', -n

/// Create a new BDD with a given ordering.  
let mk_bdd ord = 
    Bdd ((undefined, undefined, 2), ord)

/// Extract the ordering field of a BDD. 
let order (Bdd (_, ord)) p1 p2 =
    (p2 = "" && p1 <> "")
    || ord p1 p2

/// Threading state through.  
let thread s g (f1, x1) (f2, x2) =
    let s', y1 = f1 s x1
    let s'', y2 = f2 s' x2
    g s'' (y1, y2)

/// Perform an AND operation on BDDs, maintaining canonicity.
let rec bdd_and (bdd,comp as bddcomp) (m1, m2) =
    if m1 = -1 || m2 = -1 then bddcomp, -1
    elif m1 = 1 then bddcomp, m2 
    elif m2 = 1 then bddcomp, m1
    else
        try bddcomp, apply comp (m1, m2)
        with Failure _ ->
            try bddcomp, apply comp (m2, m1)
            with Failure _ ->
                let p1, l1, r1 = expand_node bdd m1
                let p2, l2, r2 = expand_node bdd m2
                let p, lpair, rpair =
                    if p1 = p2 then p1, (l1, l2), (r1, r2)
                    elif order bdd p1 p2 then p1, (l1, m2), (r1, m2)
                    else p2, (m1, l2), (m1, r2)
                let (bdd', comp'), (lnew, rnew) =
                    thread bddcomp (fun s z -> s, z) (bdd_and, lpair) (bdd_and, rpair)
                let bdd'', n = mk_node bdd' (p, lnew, rnew)
                (bdd'', ((m1, m2) |-> n) comp'), n

/// Perform an OR operation on BDDs, maintaining canonicity.
let bdd_or bdc (m1, m2) = 
    let bdc1, n = bdd_and bdc (-m1, -m2)
    bdc1, -n

/// Perform an IMP operation on BDDs, maintaining canonicity.
let bdd_imp bdc (m1, m2) = 
    bdd_or bdc (-m1, m2)

/// Perform an IFF operation on BDDs, maintaining canonicity.
let bdd_iff bdc (m1, m2) =
    thread bdc bdd_or (bdd_and, (m1, m2)) (bdd_and, (-m1, -m2))

/// Term to BDD conversion.  
let rec mkbdd (bdd,comp as bddcomp) fm =
    match fm with
    | False _ ->
        bddcomp, -1
    | True _ ->
        bddcomp, 1
    | Atom s ->
        let bdd', n = mk_node bdd (s, 1, -1) 
        (bdd', comp), n
    | Not p ->
        let bddcomp', n = mkbdd bddcomp p
        bddcomp', -n
    | And (p, q) ->
        thread bddcomp bdd_and (mkbdd, p) (mkbdd, q)
    | Or (p, q)  ->
        thread bddcomp bdd_or (mkbdd, p) (mkbdd, q)
    | Imp (p, q) ->
        thread bddcomp bdd_imp (mkbdd, p) (mkbdd, q)
    | Iff (p, q) ->
        thread bddcomp bdd_iff (mkbdd, p) (mkbdd, q)
    | _ -> failwith "mkbdd"

/// Checks for tautology based on dinary decision diagrams
let bddtaut fm = 
    snd (mkbdd (mk_bdd (<), undefined) fm) = 1

// ------------------------------------------------------------------------- //
// Towards a more intelligent treatment of "definitions".                    //
// ------------------------------------------------------------------------- //

let dest_nimp fm =
    match fm with
    | Not p -> p, false_tm
    | _ -> dest_imp fm

let rec dest_iffdef fm =
    match fm with
    | Iff (Atom x, r)
    | Iff (r, Atom x) ->
        x,r
    | _ -> failwith "not a defining equivalence"

let restore_iffdef (x,e) fm =
    mk_imp (mk_eq (x + ":bool" |> parse_term, e), fm)

let suitable_iffdef defs (x, q) =
    let fvs = 
        atoms q 
        |> List.map (Term.dest_var >> fst)
    defs
    |> List.exists (fun (x', _) ->
        mem x' fvs)
    |> not

let rec sort_defs (acc:(string * term) list) 
    (defs:(string * term) list) fm =
    try 
        let x, e =
            defs |> List.find (suitable_iffdef defs)
        let ps, nonps =
            defs |> List.partition (fun (x', _) -> x' = x)
        let ps' = subtract ps [x, e]
        sort_defs ((x, e) :: acc) nonps (List.foldBack restore_iffdef ps' fm)
    with _ ->
        List.rev acc, List.foldBack restore_iffdef defs fm

// ------------------------------------------------------------------------- //
// Improved setup.                                                           //
// ------------------------------------------------------------------------- //

let rec mkbdde sfn (bdd,comp as bddcomp) fm =
    match fm with
    | False _ ->
        bddcomp, -1
    | True _ ->
        bddcomp, 1
    | Atom s ->
        try bddcomp, apply sfn s
        with _ ->
            let bdd', n = mk_node bdd (s, 1, -1)
            (bdd', comp), n
    | Not p ->
        let bddcomp', n = mkbdde sfn bddcomp p
        bddcomp', -n
    | And (p, q) ->
        thread bddcomp bdd_and (mkbdde sfn, p) (mkbdde sfn, q)
    | Or (p, q)  ->
        thread bddcomp bdd_or (mkbdde sfn, p) (mkbdde sfn, q)
    | Imp (p, q) ->
        thread bddcomp bdd_imp (mkbdde sfn, p) (mkbdde sfn, q)
    | Iff (p, q) ->
        thread bddcomp bdd_iff (mkbdde sfn, p) (mkbdde sfn, q)
    | _ -> failwith "mkbdde"

let rec mkbdds sfn bdd defs fm =
    match defs with
    | [] -> mkbdde sfn bdd fm
    | (p, e) :: odefs ->
        let bdd', b = mkbdde sfn bdd e
        mkbdds ((p |-> b) sfn) bdd' odefs fm

let ebddtaut fm =
    let l, r =
        try dest_nimp fm
        with _ -> true_tm, fm
    let eqs, noneqs =
        let parFun fm =
            try
                dest_iffdef fm |> ignore
                true
            with _ -> false
        List.partition parFun (strip_conj l)
    let mk_imp tm1 tm2 = mk_imp (tm1,tm2) 
    let defs, fm' = 
        sort_defs [] (List.map dest_iffdef eqs) 
            (List.foldBack mk_imp noneqs r)
    snd (mkbdds undefined (mk_bdd (<), undefined) defs fm') = 1
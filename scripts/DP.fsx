#I "../src/bin/Debug/net7.0"
#r "nholz.dll"

open HOL
open HOL.AutomatedReasoning

// fsi.AddPrinter print_type
// fsi.AddPrinter print_qtype
// fsi.AddPrinter print_term
// fsi.AddPrinter print_qterm
// fsi.AddPrinter print_thm

CoreThry.load
Equal.load
Bool.load

# time;;
tautology(prime 11)
// Real: 00:00:02.052, CPU: 00:00:02.070, GC gen0: 72, gen1: 1, gen2: 0
# time;;

# time;;
dptaut(prime 11)
// Real: 00:00:00.899, CPU: 00:00:00.950, GC gen0: 18, gen1: 1, gen2: 0
// fails from 16
# time;;

# time;;
dplltaut(prime 11)
// Real: 00:00:00.243, CPU: 00:00:00.240, GC gen0: 3, gen1: 0, gen2: 0
# time;;

# time;;
dplitaut(prime 11)
// Real: 00:00:00.629, CPU: 00:00:00.640, GC gen0: 8, gen1: 1, gen2: 0
# time;;

let rec conjToClauses tm = 
    match tm with
    | And (p, q) ->
        union (conjToClauses p) (conjToClauses q)
    | Or (p, q) ->
        distrib (conjToClauses p) (conjToClauses q)
    | _ -> [[tm]]

let clausesToConj (xs:term list list) = 
    match xs with
    | [] -> true_tm
    | xs when xs |> List.contains [] -> false_tm
    | _ -> 
        xs
        |> List.map (fun ys -> list_mk_disj ys)
        |> list_mk_conj

let clauses = 
    @"(a \/ b) /\ (~a \/ b) /\ (~a \/ d) /\ (c) /\ (~c \/ b \/ ~d) /\ (c \/ d) /\ (a \/ ~d)"
    |> parse_term
    |> conjToClauses

let one_literal_rule clauses =
    let u = List.head (List.find (fun cl -> List.length cl = 1) clauses)
    let u' = negate u
    let clauses1 = List.filter (fun cl -> not (mem u cl)) clauses
    image (fun cl -> subtract cl [u']) clauses1

@"(p) /\ (p \/ q) /\ (~p \/ r \/ s)"
|> parse_term
|> conjToClauses
|> one_literal_rule

clauses
|> one_literal_rule
|> clausesToConj

let affirmative_negative_rule clauses =
    let neg',pos = List.partition negative (unions clauses)
    let neg = image negate neg'
    let pos_only = subtract pos neg 
    let neg_only = subtract neg pos
    let pureLitterals = union pos_only (image negate neg_only)
    if pureLitterals = [] then 
        failwith "affirmative_negative_rule" 
    else
        List.filter (fun cl -> intersect cl pureLitterals = []) clauses

@"(p \/ q) /\ (~p \/ q) /\ (~p \/ t) /\ (q \/ ~t)"
|> parse_term
|> conjToClauses
|> affirmative_negative_rule

clauses
|> one_literal_rule
// |> unions
// |> List.partition negative
// |> fun (neg',pos) -> image negate neg', pos
// |> fun (neg,pos) -> subtract pos neg, subtract neg pos
// |> fun (pos_only, neg_only) -> union pos_only (image negate neg_only)
|> affirmative_negative_rule
|> clausesToConj

let resolve_on p clauses =
    let p' = negate p 
    let pos, notpos = List.partition (mem p) clauses
    let neg, other = List.partition (mem p') notpos
    let res0 =
        let pos' = image (List.filter (fun l -> l <> p)) pos
        let neg' = image (List.filter (fun l -> l <> p')) neg
        allpairs union pos' neg'
    let clauses' = union other (List.filter (not << trivial) res0)
    clauses'

@"(p \/ q) /\ (~p \/ r)"
|> parse_term
|> conjToClauses
|> resolve_on ("p:bool" |> parse_term)

clauses
|> one_literal_rule
|> affirmative_negative_rule
|> resolve_on ("a:bool" |> parse_term)
|> clausesToConj

// to choose the best litteral we need to now the resolution blowup

let resolution_blowup cls l =
    let m = List.length (List.filter (mem l) cls)
    let n = List.length (List.filter (mem (negate l)) cls)
    m * n - m - n

clauses
|> one_literal_rule
|> affirmative_negative_rule
|> fun cls -> resolution_blowup cls ("a:bool" |> parse_term)

// ------------------------------------------------------------------------- //
// Find list member that maximizes or minimizes a function.                  //
// ------------------------------------------------------------------------- //

/// finds the element of a list l that maximizes or minimizes a function f 
/// based on the given ord.
/// 
/// Support function for use with maximize and minimize.
let optimize ord f lst =
    lst
    |> List.map (fun x -> x, f x)
    |> List.reduceBack (fun (_, y1 as p1) (_, y2 as p2) ->
        if ord y1 y2 then p1 else p2)
    |> fst
                        
/// finds the element of a list l that maximizes a function f
/// 
/// maximize ((*) -1) [-1;2;3] returns -1
let maximize f l =
    optimize (>) f l
    
/// finds the element of a list l that minimizes a function f
/// 
/// minimize ((*) -1) [-1;2;3] returns 3
let minimize f l =
    optimize (<) f l

let resolution_rule clauses =
    let pvs = List.filter positive (unions clauses)
    let p = minimize (resolution_blowup clauses) pvs
    resolve_on p clauses

@"(a \/ b) /\ (~a \/ b) /\ (~a \/ d) /\ (c) /\ (~c \/ b \/ ~d) /\ (c \/ d) /\ (a \/ ~d)"
|> parse_term
|> conjToClauses
|> one_literal_rule
|> affirmative_negative_rule
|> resolution_rule
|> clausesToConj

// ------------------------------------------------------------------------- //
// Overall procedure.                                                        //
// ------------------------------------------------------------------------- //

let rec dp clauses =
    if clauses = [] then true 
    elif mem [] clauses then false 
    else
        try 
            dp (one_literal_rule clauses) 
        with 
            Failure _ ->
                try 
                    dp (affirmative_negative_rule clauses) 
                with Failure _ ->
                    dp(resolution_rule clauses)

// ------------------------------------------------------------------------- //
// Davis-Putnam satisfiability tester and tautology checker.                 //
// ------------------------------------------------------------------------- //

let dpsat fm = dp (defcnfs fm)

let dptaut fm = not (dpsat (mk_not fm))

// ------------------------------------------------------------------------- //
// Iterative implementation with explicit trail instead of recursion.        //
// ------------------------------------------------------------------------- //

type trailmix = Guessed | Deduced

let unassigned =
    let litabs p = 
        match p with
        | Not q -> q
        | _ -> p
    fun cls trail ->
        subtract (unions (image (image litabs) cls))
            (image (litabs << fst) trail)
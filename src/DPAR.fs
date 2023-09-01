/// The Davis-Putnam and Davis-Putnam-Loveland-Logemann procedures.
/// 
/// The module is the porting of the file dp.ml from the code 
/// that accompanies the book "handbook of practical logic and automated 
/// reasoning" (https://www.cl.cam.ac.uk/~jrh13/atp/)
/// adapted to fit nholz HOL system.
/// 
/// Many of the implementations are based on the version of the code ported in 
/// F# by https://github.com/jack-pappas/fsharp-logic-examples/.
[<AutoOpen>]
module HOL.AutomatedReasoning.DP

open HOL

// ========================================================================= //
// The Davis-Putnam procedure                                                //
// ========================================================================= //

let containOneLitterals clauses = 
    clauses |> List.exists (List.length >> (=) 1)

/// Implements the 1-litteral rule also called unit propagation.
/// 
/// If p is a unit clause, remove any clause containing p and remove any 
/// instance of -p from the other clauses. 
/// 
/// For example, it reduces SAT of [[p];[p;q];[-p;r;s]] to [[r;s]]
let one_literal_rule clauses =
    let u = List.head (List.find (fun cl -> List.length cl = 1) clauses)
    let u' = negate u
    let clauses1 = List.filter (fun cl -> not (mem u cl)) clauses
    image (fun cl -> subtract cl [u']) clauses1

let containPureLitterals clauses = 
    let neg',pos = List.partition negative (unions clauses)
    let neg = image negate neg'
    let pos_only = subtract pos neg 
    let neg_only = subtract neg pos
    union pos_only (image negate neg_only)
    |> List.length > 0

/// Implements the affermative-negative rule also called the 
/// pure litteral rule.
/// 
/// If a litteral occurs either only positively or only negatively 
/// delete al clauses containing that literal.
/// 
/// For example it reduces SAT of [[p;q];[-p;q];[-p;t];[q;-t]] to [-p;t]
/// where q in this case is the pure litteral.
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

/// Implements the rule for eliminating atomic formula also called the 
/// resolution rule.
/// 
/// If p occurs positively in one clasue [p;q1;...;qn] and negatively in 
/// an other [~p;r1;...;rn], remove p from both and create a unique clause 
/// from the remaining parts [q1;...;qn;r1;...;rn].
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

/// This is a supporting function that predicts the change in the number of 
/// clauses resulting from resolution on a choosen litteral l. We will pick 
/// the literal that minimizes this blowup.
let resolution_blowup cls l =
    let m = List.length (List.filter (mem l) cls)
    let n = List.length (List.filter (mem (negate l)) cls)
    m * n - m - n

/// Implements the rule for eliminating atomic formula also called the 
/// resolution rule choosing the litteral that minimize resulotion 
/// blowup.
let resolution_rule clauses =
    let pvs = List.filter positive (unions clauses)
    let p = minimize (resolution_blowup clauses) pvs
    resolve_on p clauses

// ------------------------------------------------------------------------- //
// Overall procedure.                                                        //
// ------------------------------------------------------------------------- //

/// Implements the Davis-Putnam procedure to check the satisfiability 
/// of a given list of clauses.
let rec dp clauses =
    if clauses = [] then 
        true 
    else if mem [] clauses then 
        false 
    else if clauses |> containOneLitterals then 
        dp (one_literal_rule clauses)
    else if clauses |> containPureLitterals then
        dp (affirmative_negative_rule clauses)
    else
        dp (resolution_rule clauses)

// ------------------------------------------------------------------------- //
// Davis-Putnam satisfiability tester and tautology checker.                 //
// ------------------------------------------------------------------------- //

/// Satisfiability tester based on Davis-Putnam procedure
let dpsat fm = dp (defcnfs fm)

/// Tautology tester based on Davis-Putnam procedure
let dptaut fm = not (dpsat (mk_not fm))

// ========================================================================= //
// The Davis-Putnam-Loveland-Logemann procedure.                             //
// ========================================================================= //

/// Supporting function to calculate which is the more convenient 
/// litteral to choose for the splitting rule in the 
/// Davis-Putnam-Loveland-Logemann procedure.
let posneg_count cls l =
    let m = List.length (List.filter (mem l) cls)                 
    let n = List.length (List.filter (mem (negate l)) cls)
    m + n

/// Implements the Davis-Putnam-Loveland-Logemann procedure to check the 
/// satisfiability of a given list of clauses.
let rec dpll clauses =
    if clauses = [] then 
        true 
    else if mem [] clauses then 
        false 
    else if clauses |> containOneLitterals then 
        dpll (one_literal_rule clauses)
    else if clauses |> containPureLitterals then
        dpll (affirmative_negative_rule clauses)
    else
        let pvs = List.filter positive (unions clauses)
        let p = maximize (posneg_count clauses) pvs
        dpll (insert [p] clauses) || dpll (insert [negate p] clauses)

/// Satisfiability tester based on Davis-Putnam-Loveland-Logemann procedure
let dpllsat fm = dpll (defcnfs fm)

/// Tautology tester based on Davis-Putnam-Loveland-Logemann procedure
let dplltaut fm = not (dpllsat (mk_not fm))

// ------------------------------------------------------------------------- //
// Iterative implementation with explicit trail instead of recursion.        //
// ------------------------------------------------------------------------- //

/// flag discriminitaing the litteral in the trail from dpli
type trailmix = 
    /// litteral just assumed as one half of a case-split
    | Guessed 
    /// litteral deduced by unit propagation from literals assumed earlier
    | Deduced

/// Indicates which atomic formulas in the problem have no assignment either 
/// way in the dpli trail.
let unassigned =
    let litabs p = 
        match p with
        | Not q -> q
        | _ -> p
    fun cls trail ->
        subtract (unions (image (image litabs) cls))
            (image (litabs << fst) trail)

/// Performs unit propagation until either no further progress is possible 
/// or the empty clause is derived.
/// 
/// Modifies the problem clauses `cls`, and also processes the trail 
/// `trail` into a ﬁnite partial function `fn`.
let rec unit_subpropagate (cls, fn, trail) =
    let cls' = List.map (List.filter (not << defined fn << negate)) cls
    let uu = function
        | [c] when not (defined fn c) -> [c]
        | _ -> failwith ""
    let newunits = unions (mapfilter uu cls')
    if newunits = [] then
        cls', fn, trail
    else
        let trail' = List.foldBack (fun p t -> (p, Deduced) :: t) newunits trail
        let fn' = List.foldBack (fun u -> u |-> ()) newunits fn
        unit_subpropagate (cls', fn', trail')

/// Performs unit propagation until either no further progress is possible 
/// or the empty clause is derived (by unit_subpropagate) and returns both 
/// the modiﬁed clauses and the trail.
let unit_propagate (cls, trail) =
    let fn = List.foldBack (fun (x, _) -> x |-> ()) trail undefined
    let cls', fn', trail' = unit_subpropagate (cls, fn, trail)
    cls', trail'

/// Removes items from the trail until we reach the most recent decision 
/// literal or there are no such items left at all.
let rec backtrack trail =
    match trail with
    | (p, Deduced) :: tt ->
        backtrack tt
    | _ -> trail

let rec dpli cls trail =
    let cls', trail' = unit_propagate (cls, trail)
    if mem [] cls' then 
    // if the empty clause is derived a conflict has been reached, 
    // so try to backtrack.
        match backtrack trail with
        | (p, Guessed) :: tt ->
            dpli cls ((negate p, Deduced) :: tt)
        // if in the trail there are no more other guesses to try, 
        // the list of clauses is unsatisfiabile
        | _ -> false
    else
        match unassigned cls trail' with
        // if the list of clauses is empty, satifiability is proved
        | [] -> true
        // else choose the more convenient litteral for the splitting rule
        // and add that litteral to the trail
        | ps ->
            let p = maximize (posneg_count cls') ps
            dpli cls ((p, Guessed) :: trail')

let dplisat fm = dpli (defcnfs fm) []

let dplitaut fm = not (dplisat (mk_not fm))
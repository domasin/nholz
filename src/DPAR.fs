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
// The Davis-Putnam and Davis-Putnam-Loveland-Logemann procedures.           //
// ========================================================================= //

// ------------------------------------------------------------------------- //
// The DP procedure.                                                         //
// ------------------------------------------------------------------------- //

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

/// This is a supporting function thant prredicts the change in the number of 
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
    if clauses = [] then true else if mem [] clauses then false 
    else
        try dp (one_literal_rule clauses) with _ ->
        try dp (affirmative_negative_rule clauses) with _ ->
        dp (resolution_rule clauses)

// ------------------------------------------------------------------------- //
// Davis-Putnam satisfiability tester and tautology checker.                 //
// ------------------------------------------------------------------------- //

/// Satisfiability tester based on Davis-Putnam procedure
let dpsat fm = dp (defcnfs fm)

/// Tautology tester based on Davis-Putnam procedure
let dptaut fm = not (dpsat (mk_not fm))
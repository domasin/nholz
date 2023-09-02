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


/// Creates 'triplets' of the form li ⇔ lj ⊗ lk with the literals li 
/// representing subformulas of the original formula (as in the 3-CNF 
/// procedure).
let triplicate tm =
    let p, defs, _ =
        let tm' = nenf tm
        let n = 
            (bigint 1) + overatoms (max_varindex "p_" << pname) tm' (bigint 0)
        maincnf (tm', undefined, n)
    p, List.map (snd << snd) (graph defs)

@"a ==> b /\ c"
|> parse_term
|> triplicate

/// Returns a literal without any negative sign.
let atom lit =
    if negative lit then negate lit else lit

// atom (mk_not p)

/// To identifyequivalences that are essentially the same (e.g. p <=> -q, 
/// -q <=> p and q <=> -p). forces alignment of each p <=> q such that 
/// the atom on the right is no bigger than the one on the left, and 
/// the one on the left is never negated:
let rec align (p, q) =
    if atom p < atom q then
        align (q, p)
    elif negative p then
        negate p, negate q
    else p, q

let t1 = @"~q" |> parse_term
let t2 = @"~q <=> p" |> parse_term

align (t2,t1)

/// Ensures that if `p` and `q` are to be identified (considered equivalent) 
/// also `~p` and `~q` are identified.
let equate2 (p, q) eqv =
    equate (negate p, negate q) (equate (p, q) eqv)


/// Adds to the class of equivalent equivalences also those that already follow 
/// from the existing equivalence, including the immediately trivial p <=> p.
let rec irredundant rel eqs =
    match eqs with
    | [] -> []
    | (p, q) :: oth ->
        if canonize rel p = canonize rel q then
            irredundant rel oth
        else
            insert (p, q) (irredundant (equate2 (p, q) rel) oth)

/// Takes an assumed equivalence peq and triplet fm, together with a list of 
/// putative equivalences eqs. It returns an irredundant set of those 
/// equivalences from eqs that follow from peq and fm together
let consequences (p, q as peq) fm eqs =
    let follows (r, s) =
        tautology <| mk_imp (mk_conj (mk_eq (p, q), fm), mk_eq (r, s))

    irredundant (equate2 peq unequal) (List.filter follows eqs)

let triggers fm =
    let poslits = insert true_tm (List.map (fun p -> p) (atoms fm))
    let lits = union poslits (List.map negate poslits)
    let pairs = allpairs (fun p q -> p, q) lits lits
    let npairs = List.filter (fun (p, q) -> atom p <> atom q) pairs
    let eqs = setify <| List.map align npairs
    let raw = List.map (fun p -> p, consequences p fm eqs) eqs
    List.filter (fun (p, c) -> not <| List.isEmpty c) raw

let trigger =
    let triggers = 
        [
            parse_term "p <=> q /\ r";
            parse_term @"p <=> q \/ r";
            parse_term "p <=> (q ==> r)";
            parse_term "p <=> (q <=> r)"; 
        ]
        |> List.map triggers
    match triggers with
    | [trig_and; trig_or; trig_imp; trig_iff] ->
        let ddnegate fm =
            match fm with
            | Not (Not p) -> p
            | _ -> fm
        let inst_fn xs = 
            match xs with 
            | [x; y; z] ->
                let subfn = fpf ["p";"q";"r"] [x; y; z]
                ddnegate << psubst subfn
            | _ -> failwith "trigger inst_fn"
        let inst2_fn i (p, q) =
            align (inst_fn i p, inst_fn i q)
        let instn_fn i (a, c) =
            inst2_fn i a, List.map (inst2_fn i) c
        let inst_trigger = List.map << instn_fn
        function
            | Iff (x, And (y, z)) ->
                inst_trigger [x; y; z] trig_and
            | Iff (x, Or (y, z)) ->
                inst_trigger [x; y; z] trig_or
            | Iff (x, Imp (y, z)) ->
                inst_trigger [x; y; z] trig_imp
            | Iff (x, Iff (y, z)) ->
                inst_trigger [x; y; z] trig_iff
            | _ ->
                failwith "How did we get here?"
    | _ ->
        failwith "How did we get here?"

let fn =  ("q" |-> ("x:bool" |> parse_term)) Empty

@"p <=> q /\ r" 
|> parse_term
|> psubst fn

@"x <=> ~(q /\ r)" 
|> parse_term
|> trigger

let trigger2 =
    let [trig_and; trig_or; trig_imp; trig_iff] = 
         [parse_term "p <=> q /\ r";
            parse_term @"p <=> q \/ r";
            parse_term "p <=> (q ==> r)";
            parse_term "p <=> (q <=> r)"; ]
        |> List.map triggers
    let ddnegate fm = match fm with Not(Not p) -> p | _ -> fm in
    let inst_fn xs = 
            match xs with 
            | [x; y; z] ->
                let subfn = fpf ["p";"q";"r"] [x; y; z]
                ddnegate << psubst subfn
            | _ -> failwith "trigger inst_fn"
    let inst2_fn i (p, q) =
            align (inst_fn i p, inst_fn i q)
    let instn_fn i (a, c) =
        inst2_fn i a, List.map (inst2_fn i) c
    let inst_trigger = List.map << instn_fn
    function 
        | (Iff(x,And(y,z))) -> inst_trigger [x;y;z] trig_and
        | (Iff(x,Or(y,z))) -> inst_trigger [x;y;z] trig_or
        | (Iff(x,Imp(y,z))) -> inst_trigger [x;y;z] trig_imp
        | (Iff(x,Iff(y,z))) -> inst_trigger [x;y;z] trig_iff
/// Binary decision diagrams (BDDs) using complement edges. 
/// 
/// The module is the porting of the union-find algorithm defined in the file 
/// fol.ml from the code that accompanies the book "handbook of practical 
/// logic and automated reasoning" (https://www.cl.cam.ac.uk/~jrh13/atp/) 
/// adapted to fit nholz HOL system.
/// 
/// Many of the implementations are based on the version of the code ported in 
/// F# by https://github.com/jack-pappas/fsharp-logic-examples/.
[<AutoOpen>]
module HOL.AutomatedReasoning.Fol

open HOL

/// type for folTerms
type folTerm = 
    | Var of string
    | Fn of string * folTerm list

// Active patternrs to convert HOL terms to FOL terms

let (|FolNumeral|_|) tm =
    match tm |> is_numeral_tag with
    | true -> 
        tm 
        |> print_term
        |> Some
    | _ -> None

let (|FolFn|_|) tm =
    match tm |> is_comb && not (tm |> is_bool_term) with
    | true -> 
        tm 
        |> strip_comb 
        |> fun (t,tl) -> t |> dest_const |> fst, tl
        |> Some
    | _ -> None

let (|FolVar|_|) tm =
    match tm |> is_var with
    | true -> 
        tm |> dest_var |> fst |> Some
    | _ -> None

/// Converts a suitable HOL term in a FOL term
let rec termToFolTerm tm = 
    match tm with
    | FolNumeral x -> Fn (x,[])
    | FolVar x -> Var x
    | FolFn (f,args) -> 
        let folArgs = 
            args 
            |> List.map (termToFolTerm)
        Fn (f,folArgs)
    | _ -> failwith "not a fol term"

/// type for atomic first order formulas
type fol = 
    R of string * folTerm list

/// Polymorphic type of formulas
type formula<'a> =
    | False
    | True
    | Atom of 'a
    | Not of formula<'a>
    | And of formula<'a> * formula<'a>
    | Or of formula<'a> * formula<'a>
    | Imp of formula<'a> * formula<'a>
    | Iff of formula<'a> * formula<'a>
    | Forall of string * formula<'a>
    | Exists of string * formula<'a>

// Active patters for converting suitable HOL terms to FOL formulas

let (|FalseFormula|_|) tm =
    match tm with
    | Tmconst ("false", Tycomp ("bool", [])) -> Some false_tm
    | _ -> None

let (|TrueFormula|_|) tm =
    match tm with
    | Tmconst ("true", Tycomp ("bool", [])) -> Some true_tm
    | _ -> None

let (|NotFormula|_|) tm =
    match tm |> is_not with
    | true -> Some (tm |> dest_not)
    | _ -> None

let (|AndFormula|_|) tm =
    match tm |> is_conj with
    | true -> tm |> dest_conj |> Some
    | _ -> None

let (|OrFormula|_|) tm =
    match tm |> is_disj with
    | true -> tm |> dest_disj |> Some
    | _ -> None

let (|ImpFormula|_|) tm =
    match tm |> is_imp with
    | true -> tm |> dest_imp |> Some
    | _ -> None

let (|IffFormula|_|) tm =
    match tm |> is_eq with
    | true -> 
        let x,y = tm |> dest_eq 
        match x |> is_bool_term && y |> is_bool_term with
        | true -> Some (x,y)
        | _ -> None
    | _ -> None

let (|ForallFormula|_|) tm =
    match tm |> is_forall with
    | true -> Some(tm |> dest_forall)
    | _ -> None

let (|ExistsFormula|_|) tm =
    match tm |> is_exists with
    | true -> Some(tm |> dest_exists)
    | _ -> None

let (|Rel|_|) tm =
    match tm |> is_comb && tm |> is_bool_term with
    | true -> 
        tm 
        |> strip_comb 
        |> fun (t,tl) -> t |> dest_const |> fst, tl
        |> Some
    | _ -> None

/// Converts a suitable HOL term in a FOL formula
let rec termToFolFormula tm =
    // printfn "%s" (tm |> print_term)
    match tm with
    | FalseFormula _-> 
        // printfn "False"
        False
    | TrueFormula _ -> 
        // printfn "True"
        True
    | NotFormula p ->
        // printfn "not"
        Not (p |> termToFolFormula)
    | AndFormula (p, q) ->
        // printfn "and"
        And (p |> termToFolFormula, q |> termToFolFormula)
    | OrFormula(p, q) ->
        // printfn "or"
        Or (p |> termToFolFormula, q |> termToFolFormula)
    | ImpFormula(p, q) ->
        // printfn "imp"
        Imp (p |> termToFolFormula, q |> termToFolFormula)
    | IffFormula(p, q) ->
        // printfn "iff"
        Iff (p |> termToFolFormula, q |> termToFolFormula)
    | ForallFormula (x, p) ->
        // printfn "forall"
        Forall (x |> dest_var |> fst, p |> termToFolFormula)
    | ExistsFormula (x, p) ->
        // printfn "exists"
        Exists (x |> dest_var |> fst, p |> termToFolFormula)
    | Rel (r, args) ->
        // printfn "rel"
        Atom (R (r, args |> List.map termToFolTerm))
    | _ -> failwith "not fol formula"

// ------------------------------------------------------------------------- //
// Semantics, implemented of course for finite domains only.                 //
// ------------------------------------------------------------------------- //

/// Returns the value of a FOL term in a particular 
/// interpretation M and valuation v
let rec termval (domain, func, pred as m) v tm =
    match tm with
    | Var x ->
        apply v x
    | Fn (f, args) ->
        func f (List.map (termval m v) args)

/// Evaluates a fol formula in the intepretation specified
/// by the triplet domain, func, pred and the variables valuation v.
let rec holds (domain, func, pred) v fm =
    let m = domain, func, pred
    match fm with
    | False -> false
    | True -> true
    | Atom (R (r, args)) ->
        pred r (List.map (termval m v) args)
    | Not p ->
        not(holds m v p)
    | And (p, q) ->
        (holds m v p) && (holds m v q)
    | Or (p, q) ->
        (holds m v p) || (holds m v q)
    | Imp (p, q) ->
        not(holds m v p) || (holds m v q)
    | Iff (p, q) ->
        (holds m v p = holds m v q)
    | Forall (x, p) ->
        List.forall (fun a -> holds m ((x |-> a) v) p) domain
    | Exists (x, p) ->
        List.exists (fun a -> holds m ((x |-> a) v) p) domain

// ------------------------------------------------------------------------- //
// Examples of particular interpretations.                                   //
// ------------------------------------------------------------------------- //

/// An interpretation à la Boole
let bool_interp =
    let func f args =
        match f, args with
        | "0", [] -> false
        | "1", [] -> true
        | "+", [x; y] -> not (x = y)
        | "*", [x; y] -> x && y
        | _ -> failwith "uninterpreted function"

    let pred p args =
        match p, args with
        | "=", [x; y] -> x = y
        | _ -> failwith "uninterpreted predicate"

    [false; true], func, pred

/// An arithmetic modulo n interpretation
let mod_interp n =
    let func f args =
        match f, args with
        | "0", [] -> 0
        | "1", [] -> 1 % n
        | "+", [x; y] -> (x + y) % n
        | "*", [x; y] -> (x * y) % n
        | _ -> failwith "uninterpreted function"

    let pred p args =
        match p, args with
        | "=", [x; y] -> x = y
        | _ -> failwith "uninterpreted predicate"

    [0..(n - 1)], func, pred

/// Free variables in FOL terms. 
let rec fvt tm =
    match tm with
    | Var x -> [x]
    | Fn (f, args) ->
        unions <| List.map fvt args
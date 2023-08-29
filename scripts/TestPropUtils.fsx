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

// let psubst subfn =
//     onatoms <| fun p ->
//         tryapplyd subfn p (p + ":bool" |> parse_term)

psubst ("p" |=> (@"p /\ q" |> parse_term)) (@"p ==> q" |> parse_term)

let p = @"p:bool" |> parse_term |> fun x -> printfn "%s" (x.ToString())

@"p /\ q ==> q /\ r"
|> parse_term
|> print_truthtable

@"((p ==> q) ==> p) ==> p"
|> parse_term
|> print_truthtable

@"~ true <=> false"
|> parse_term
|> tautology

@"p /\ (q /\ r) <=> (p /\ q) /\ r"
|> parse_term
|> tautology

@"(true ==> (x <=> false)) ==> ~(y \/ false /\ z)"
|> parse_term
|> psimplify

let univ = @"! P x. P x" |> parse_term

let x = "x:bool" |> parse_term

@"(true ==> (x <=> false)) ==> ~(y \/ false /\ z)"
|> parse_term
|> subst [x,univ]
|> psimplify

@"((x ==> y) ==> true) \/ ~ false"
|> parse_term
|> psimplify

// let fm =  
//     @"(p <=> q) <=> ~(r ==> s)"
//     |> parse_term

// let fm' = 
//     fm
//     |> nnf

// tautology (mk_eq (fm,fm'))

@"(p ==> p') /\ (q ==> q') ==> (p /\ q ==> p' /\ q')"
|> parse_term
|> tautology

@"p ==> q"
|> parse_term
|> print_truthtable

@"(~p /\ ~q) \/ (~p /\ q) \/ (p /\ q)"
|> parse_term
|> print_truthtable


// let fm = @"(p \/ q /\ r) /\ (~p \/ ~r)" |> parse_term

// dnfOrig fm

// fm |> print_truthtable

// ------------------------------------------------------------------------- //
// DNF via distribution.                                                     //
// ------------------------------------------------------------------------- //

@"(p \/ q /\ r) /\ (~p \/ ~r)"
|> parse_term
|> rawdnf

// ------------------------------------------------------------------------- //
// A dnf version using a list representation.                                //
// ------------------------------------------------------------------------- //

@"(p \/ q /\ r) /\ (~p \/ ~r)"
|> parse_term
|> purednf

// ------------------------------------------------------------------------- //
// Filtering out trivial disjuncts (in this guise, contradictory).           //
// ------------------------------------------------------------------------- //

@"(p \/ q /\ r) /\ (~p \/ ~r)"
|> parse_term
|> purednf
|> filter (not << trivial)

// ------------------------------------------------------------------------- //
// With subsumption checking, done very naively (quadratic).                 //
// ------------------------------------------------------------------------- //

// ------------------------------------------------------------------------- //
// Mapping back to a formula.                                                //
// ------------------------------------------------------------------------- //

let fm = 
    @"(p \/ q /\ r) /\ (~p \/ ~r)"
    |> parse_term

let dnfFm = fm |> dnf

tautology(mk_eq (fm,dnfFm))

@"p /\ ~p"
|> parse_term
|> dnf

@"p ==> (q /\ r)"
|> parse_term
|> dnf

@"p ==> (q /\ r)"
|> parse_term
|> cnf

@"~ (p /\ ~p)"
|> parse_term
|> cnf
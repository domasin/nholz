#I "../../src/bin/Debug/net7.0"
#r "nholz.dll"

open HOL
open HOL.PropUtils

// fsi.AddPrinter print_type
// fsi.AddPrinter print_qtype
// fsi.AddPrinter print_term
// fsi.AddPrinter print_qterm
// fsi.AddPrinter print_thm

CoreThry.load
Equal.load
Bool.load

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

let fm =  
    @"(p <=> q) <=> ~(r ==> s)"
    |> parse_term

let fm' = 
    fm
    |> nnf

tautology (mk_eq (fm,fm'))

@"(p ==> p') /\ (q ==> q') ==> (p /\ q ==> p' /\ q')"
|> parse_term
|> tautology
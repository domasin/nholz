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

stalmarck (mk_adder_test 6 3)


@"a ==> b /\ c"
|> parse_term
|> triplicate

// atom (mk_not p)

let t1 = @"~q" |> parse_term
let t2 = @"~q <=> p" |> parse_term

align (t2,t1)

let fn =  ("q" |-> ("x:bool" |> parse_term)) Empty

@"p <=> q /\ r" 
|> parse_term
|> psubst fn

@"x <=> ~(q /\ r)" 
|> parse_term
|> trigger

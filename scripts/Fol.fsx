#I "../src/bin/Debug/net7.0"
#r "nholz.dll"

open HOL
open HOL.AutomatedReasoning

// fsi.AddPrinter print_type
// fsi.AddPrinter print_qtype
// fsi.AddPrinter print_term
// fsi.AddPrinter print_qterm
// fsi.AddPrinter print_thm
// fsi.AddPrinter sprint_patricia_tree

CoreThry.load
Equal.load
Bool.load
BoolAlg.load
BoolClass.load
Pair.load
Ind.load
Nat.load
NatNumrl.load
NatArith.load
NatRel.load
NatEval.load

@"! x. (x = 0) \/ (x = 1)"
|> parse_term
|> termToFolFormula
|> holds (mod_interp 2) undefined 

@"! x. (x = 0) \/ (x = 1)"
|> parse_term
|> termToFolFormula
|> holds (mod_interp 3) undefined 

let fm =
    @"! x. ~(x = 0) ==> ? y. x * y = 1"
    |> parse_term
    |> termToFolFormula

[1..45]
|> List.filter (fun n -> 
    fm |> holds (mod_interp n) undefined
)
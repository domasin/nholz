#r "nuget: nholz2"

open HOL
open System.Numerics

fsi.AddPrinter print_type
fsi.AddPrinter print_qtype
fsi.AddPrinter print_term
fsi.AddPrinter print_qterm
fsi.AddPrinter print_thm

CoreThry.load

the_tyconsts

let unit = seq [|0|]
let bool = seq [|0;1|]

let infty =
    let rec numbersFrom n = 
        seq { 
            yield n
            yield! numbersFrom (n + 1) }

    numbersFrom 0

type Universe = 
    | P of seq<int>
    | D of seq<Universe>

P bool
D (seq [|P bool; P bool|])

let model = function 
    | ("bool", 0) -> P bool
    | ("->", 2) -> D (seq [|P bool; P bool|])

let boolModel = fun () -> P bool
let arrowModel = fun (x,y) -> P
 
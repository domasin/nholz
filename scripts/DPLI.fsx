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
dplitaut(prime 11)
// Real: 00:00:00.629, CPU: 00:00:00.640, GC gen0: 8, gen1: 1, gen2: 0
# time;;

# time;;
dplbtaut(prime 11)
// Real: 00:00:00.788, CPU: 00:00:00.820, GC gen0: 10, gen1: 1, gen2: 0
# time;;

# time;;
dplitaut(prime 101)
// Real: 00:02:30.519, CPU: 00:02:27.520, GC gen0: 1057, gen1: 31, gen2: 2
# time;;
// 15:59:33

# time;;
dplbtaut(prime 101)
// Real: 00:00:59.501, CPU: 00:00:59.190, GC gen0: 504, gen1: 16, gen2: 1
# time;;

let cls = [[p];[r;p1_];[mk_not p]]

one_literal_rule cls
unit_subpropagate (cls,Empty,[])
unit_propagate (cls,[])

let trail : (term * trailmix) list= [r,Guessed;p,Deduced]
let fn = List.foldBack (fun (x, _) -> x |-> ()) trail undefined
// let cls', fn', trail' = unit_subpropagate (cls, fn, trail)

// unit_subpropagate
let cls' = List.map (List.filter (not << defined fn << negate)) cls
let uu = function
    | [c] when not (defined fn c) -> [c]
    | _ -> failwith ""
let newunits = unions (mapfilter uu cls')
let trail' = List.foldBack (fun p t -> (p, Deduced) :: t) newunits trail
let fn' = List.foldBack (fun u -> u |-> ()) newunits fn

let cls1 = [[mk_not p]]
let fn1= (p |-> ()) Empty

cls1
|> List.map (fun xs -> 
    xs
    |> List.filter (fun x -> 
        x
        |> negate
        |> defined fn1
        |> not
    )
)







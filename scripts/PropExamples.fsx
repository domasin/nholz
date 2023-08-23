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

let s,t,n = 3,3,4
let vertices = [1..n]
let yesgrps = List.map (allsets 2) (allsets s vertices)
let nogrps = List.map (allsets 2) (allsets t vertices)

let e = function 
    | [m;n] -> "p_" + (string m) + "_" + (string n) + ":bool" |> parse_term
    | _ -> failwith "unexpected input Ramsey:e"

mk_disj (
    list_disj (List.map (list_conj << List.map e) yesgrps),
    list_disj (List.map (list_conj << List.map (fun p -> mk_not (e p))) nogrps))

let ramsey s t n =
    let vertices = [1..n]
    let yesgrps = List.map (allsets 2) (allsets s vertices)
    let nogrps = List.map (allsets 2) (allsets t vertices)
    let e = function 
        | [m;n] -> "p_" + (string m) + "_" + (string n) + ":bool" |> parse_term
        | _ -> failwith "unexpected input Ramsey:e"
    mk_disj (
        list_disj (List.map (list_conj << List.map e) yesgrps),
        list_disj (List.map (list_conj << List.map (fun p -> mk_not (e p))) nogrps))

ramsey 3 3 4
|> print_term
|> fun x -> x.Replace("\\/", "\\/\n")

tautology(ramsey 3 3 5)
tautology(ramsey 3 3 6)
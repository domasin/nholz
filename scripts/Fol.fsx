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

let (|Fn|_|) tm =
    match tm |> is_comb && not (tm |> is_bool_term) with
    | true -> 
        tm 
        |> strip_comb 
        |> fun (t,tl) -> t |> dest_const |> fst, tl
        |> Some
    | _ -> None

let (|Var|_|) tm =
    match tm |> is_var with
    | true -> 
        tm |> dest_var |> fst |> Some
    | _ -> None

let (|Rel|_|) tm =
    match tm |> is_comb && tm |> is_bool_term with
    | true -> 
        tm 
        |> strip_comb 
        |> fun (t,tl) -> t |> dest_const |> fst, tl
        |> Some
    | _ -> None

let rec termval (domain, func, pred as m) v tm =
    match tm with
    | Var x ->
        apply v x
    | Fn (f, args) ->
        func f (List.map (termval m v) args)
    | _ -> failwith "not fol term"

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

"x"
|> parse_term
|> termval bool_interp (("x" |-> true) undefined)

let rec holds (domain, func, pred) v fm =
    let m = domain, func, pred
    match fm with
    | False _ -> false
    | True _ -> true
    | Rel (r, args) ->
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
    | Forall (Var x, p) ->
        List.forall (fun a -> holds m ((x |-> a) v) p) domain
    | Exists (Var x, p) ->
        List.exists (fun a -> holds m ((x |-> a) v) p) domain
    | _ -> failwith "not fol term"

"0"
|> parse_term
|> fun x -> x.ToString()
|> termval bool_interp undefined

@"(x = 0)"
|> parse_term
|> function Rel (r, args) -> 
    args |> List.map (termval bool_interp undefined) 
|> holds bool_interp undefined 

@"(x = 0) \/ (x = 1)"
|> parse_term
|> function Or (p,q) -> p, q
|> holds bool_interp undefined 

@"! x. (x = 0) \/ (x = 1)"
|> parse_term
|> function Forall (Var x,p) -> x,p
|> holds bool_interp undefined 
#I "../src/bin/Debug/net7.0"
#r "nholz.dll"

open HOL
open HOL.AutomatedReasoning
// open System.Numerics
// open LanguagePrimitives

// fsi.AddPrinter print_type
// fsi.AddPrinter print_qtype
// fsi.AddPrinter print_term
// fsi.AddPrinter print_qterm
// fsi.AddPrinter print_thm

CoreThry.load
Equal.load
Bool.load

@"(p \/ (q /\ ~r)) /\ s"
|> parse_term
|> defcnfOrig

@"p_3 /\ (~ p_1 \/ q) /\ (~ p_1 \/ ~ r) /\ (p_1 \/ ~ q \/ r) /\ (~ p_3 \/ p_2) /\ (~ p_3 \/ s) /\ (p_3 \/ ~ p_2 \/ ~ s) /\ (~ p_2 \/ p \/ p_1) /\ (p_2 \/ ~ p) /\ (p_2 \/ ~ p_1) <=> (p \/ p_1 \/ ~p_2) /\
(p_1 \/ r \/ ~q) /\
(p_2 \/ ~p) /\
(p_2 \/ ~p_1) /\
(p_2 \/ ~p_3) /\
p_3 /\
(p_3 \/ ~p_2 \/ ~s) /\ (q \/ ~p_1) /\ (s \/ ~p_3) /\ (~p_1 \/ ~r)"
|> parse_term
|> tautology

@"~ (p \/ q /\ r) <=> ~ p /\ (~ q \/ ~ r)"
|> parse_term
|> tautology

@"(p \/ (q /\ ~r)) /\ s"
|> parse_term
|> defcnf3

// let subcnf sfn op (p, q) (fm, defs, n) =
//     let fm1, defs1, n1 = sfn (p, defs, n)
//     let fm2, defs2, n2 = sfn (q, defs1, n1) 
//     op (fm1,fm2), defs2, n2

// let rec orcnf (fm, defs, n as trip) =
//     match fm with
//     | Or (p, q) ->
//         subcnf orcnf mk_disj (p,q) trip
//     | _ -> maincnf trip

// let rec andcnf (fm, defs, n as trip) =
//     match fm with
//     | And (p, q) ->
//         subcnf andcnf mk_conj (p,q) trip
//     | _ -> orcnf trip

// let defcnfs fm =
//     mk_defcnf andcnf fm

// let defcnf fm =
//     defcnfs fm
//     |> List.map list_disj
//     |> list_conj

// @"(p \/ (q /\ ~r)) /\ s"
// |> parse_term
// |> defcnf

// @"(p \/ p_1) /\ s /\ (~ p_1 \/ q) /\ (~ p_1 \/ ~ r) /\ (p_1 \/ ~ q \/ r) <=> (p \/ p_1) /\ (p_1 \/ r \/ ~q) /\ (q \/ ~p_1) /\ s /\ (~p_1 \/ ~r)"
// |> parse_term
// |> tautology


// let mkprop (n : bigint) =
//     let name = sprintf "p_%O" n
//     (name + ":bool" |> parse_term), n + (bigint 1)

// mkprop (bigint 10)

// let rec maincnf (fm, defs, n as trip) =
//     match fm with
//     | And (p, q) ->
//         defstep mk_conj (p, q) trip
//     | Or (p, q) ->
//         defstep mk_disj (p, q) trip
//     | Iff (p, q) ->
//         defstep mk_eq (p, q) trip
//     | _ -> trip

// and defstep op (p, q) (fm, defs, n) =
//     let fm1, defs1, n1 = maincnf (p, defs, n)
//     let fm2, defs2, n2 = maincnf (q, defs1, n1)
//     let fm' = op (fm1,fm2)
//     try fst(apply defs2 fm'), defs2, n2
//     with _ ->
//         let v, n3 = mkprop n2
//         v, (fm' |-> (v, mk_eq (v, fm'))) defs2, n3

// // let matches s = 
// //     let chars = 
// //         explode s 
// //     fun c -> mem c chars

// // let numeric = matches "0123456789"

// let max_varindex pfx s (n : bigint) =
//     let m = String.length pfx
//     let l = String.length s
//     if l <= m || s.[0..m] <> pfx then n else
//     let s' = s.[m.. (l - m)]
//     if List.forall is_numeric (explode s') then
//         max n (BigInteger.Parse s')
//     else n

// let mk_defcnf fn fm =
//     let fm' = nenf fm
//     let n = GenericOne + overatoms (max_varindex "p_" << pname) fm' GenericZero
//     let fm'', defs, _ = fn (fm', undefined, n)
//     let deflist = List.map (snd << snd) (graph defs)
//     unions <| simpcnf fm'' :: List.map simpcnf deflist

// let defcnfOrig fm =
//     mk_defcnf maincnf fm
//     |> List.map list_disj
//     |> list_conj

// let fm' = nenf (@"(p /\ q)" |> parse_term)
// let n = GenericOne + overatoms (max_varindex "p_" << pname) fm' GenericZero
// let fm'', defs, _ = maincnf (fm', undefined, n)
// let deflist = List.map (snd << snd) (graph defs)
// unions <| simpcnf fm'' :: List.map simpcnf deflist

// @"p_1 <=> p /\ q"
// |> parse_term
// |> mk_not
// |> nnf
// |> function Or (p, q) -> allpairs union (purednf p) (purednf q)
// // |> purednf

// union [1;2;3] [1;5;4;3]

// setify [1;2;3;1;4;3]

// @"(p /\ q)"
// |> parse_term
// |> defcnfOrig

// @"p_1 /\ (~ p_1 \/ p) /\ (~ p_1 \/ q) /\ (p_1 \/ ~ p \/ ~ q) <=> (p \/ ~p_1) /\ p_1 /\ (p_1 \/ ~p \/ ~q) /\ (q \/ ~p_1)"
// |> parse_term
// |> tautology

// @"(p \/ (q /\ ~r)) /\ s"
// |> parse_term
// |> defcnfOrig
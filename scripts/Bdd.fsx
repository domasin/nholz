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

let bddP = "p:bool" |> parse_term |> mkbdd (mk_bdd (<), undefined)
let bddQ = "q:bool" |> parse_term |> mkbdd (mk_bdd (<), undefined)

let f1 = 
    undefined
    |> ("x" |-> 1)
    |> ("y" |-> 2)
    |> ("z" |-> 3)
// |> print_patricia_tree

let f2 = 
    undefined
    |> ("y" |-> 2)
    |> ("z" |-> 3)
    |> ("x" |-> 1)
    // |> print_patricia_tree

f1 = f2

(2 |-> ("p", 1, -1)) undefined
|> fun fn -> tryapplyd fn -2 ("", 1, 1)

@"p /\ q ==> q /\ r"
|> parse_term
|> mkbdd (mk_bdd (<), undefined)
|> fst
|> snd
|> fun bdd -> order bdd "r" "p"
// |> fun bdd -> expand_node bdd 2
// |> fun bdd -> 
//     match bdd with
//     | Bdd ((uniqueTable, expansionTable, index), ord) -> 
//         expansionTable |> sprint_patricia_tree

#time
@"/\ (out_0 <=> x_0 /\ y_0)"
|> String.replicate 2000
|> fun x -> @"(out_0 <=> x_0 /\ y_0) " + x
|> parse_term
|> bddtaut
// Real: 00:00:09.044, CPU: 00:00:09.100, GC gen0: 168, gen1: 3, gen2: 0
#time

#time
@"/\ (out_0 <=> x_0 /\ y_0)"
|> String.replicate 2000
|> fun x -> @"(out_0 <=> x_0 /\ y_0) " + x
|> parse_term
|> ebddtaut
// Real: 00:00:09.330, CPU: 00:00:09.310, GC gen0: 168, gen1: 2, gen2: 0
#time

@"/\ ((out_0 <=> x_0 /\ y_0) ==> true)"
|> String.replicate 500
|> fun x -> @"((out_0 <=> x_0 /\ y_0) ==> true) " + x
|> parse_term
|> ebddtaut

let prime50 = prime 50

#time
prime50 
|> atoms
// Real: 00:00:00.010, CPU: 00:00:00.000, GC gen0: 0, gen1: 0, gen2: 0
#time

prime50 |> bddtaut
prime50 |> ebddtaut

@"out_0 <=> x_0 /\ y_0"
|> parse_term
|> bddtaut



#time
bddtaut (prime 50)
// Real: 00:00:33.862, CPU: 00:00:35.050, GC gen0: 795, gen1: 117, gen2: 21
#time


#time
ebddtaut (prime 50)
// Real: 00:00:36.621, CPU: 00:00:36.690, GC gen0: 801, gen1: 123, gen2: 28
#time

ebddtaut (prime 19)
bddtaut (prime 19)

prime 50
|> atoms
|> List.map (Term.dest_var >> fst)

prime 50
|> free_vars


ebddtaut (prime 101)

ebddtaut (mk_adder_test 9 5)

mk_adder_test 4 2

let emptyBdd = 
    mk_bdd (<)

emptyBdd |> print_bdd

@"p:bool"
|> parse_term
|> Term.dest_var
|> fst



@"p:bool"
|> parse_term
|> mkbdd (mk_bdd (<), undefined)
|> fst
|> fst
|> fun bdd -> lookup_unique bdd (expand_node bdd 2)
    
@"p /\ q ==> q /\ r"
|> parse_term
|> mkbdd (mk_bdd (<), undefined)
|> snd

@"true"
|> parse_term
|> mkbdd (emptyBdd, undefined)
|> snd

@"a \/ ~a"
|> parse_term
|> bddtaut

@"a ==> b"
|> parse_term
|> bddtaut

@"a \/ ~a"
|> parse_term
|> dptaut

// bddtaut (mk_adder_test 4 2)

// bddtaut (prime 101)

// dptaut (mk_adder_test 4 2) // false: va controllato dovrebbe essere true

dplisat (mk_adder_test 4 2) 

dplisat (mk_not (mk_adder_test 4 2))

// dplitaut (mk_adder_test 4 2) // false: va controllato dovrebbe essere true

// tautology (mk_adder_test 4 2)

// type bddnode = 
//     term * int * int

// /// A BDD contains a variable order, unique and computed table.
// type bdd = 
//     Bdd of 
//         (func<bddnode, int> * func<int, bddnode> * int) 
//         * 
//         (term -> term -> bool)

// let print_bdd (Bdd ((unique, uback, n), ord)) =
//     printf "<BDD with %i nodes>" n

// /// Map a BDD node back to its components. 
// let expand_node (Bdd ((_, expand, _), _)) n =
//     if n >= 0 then
//         tryapplyd expand n (p, 1, 1) // p al posto di P "" 
//     else 
//         let p, l, r = tryapplyd expand -n (p, 1, 1) // p al posto di P "" 
//         p, -l, -r

// /// Lookup or insertion if not there in unique table. 
// let lookup_unique (Bdd ((unique, expand, n), ord) as bdd) node =
//     try bdd, apply unique node
//     with _ ->
//         Bdd (((node |-> n) unique, (n |-> node) expand, n + 1), ord), n

// /// Produce a BDD node (old or new).
// let mk_node bdd (s, l, r) =
//     if l = r then bdd, l
//     elif l >= 0 then
//         lookup_unique bdd (s, l, r)
//     else 
//         let bdd', n = lookup_unique bdd (s, -l, -r) 
//         bdd', -n

// /// Create a new BDD with a given ordering.  
// let mk_bdd ord = 
//     Bdd ((undefined, undefined, 2), ord)

// /// Extract the ordering field of a BDD. 
// let order (Bdd (_, ord)) p1 p2 =
//     (p2 = p && p1 <> p) // p instead of P ""
//     || ord p1 p2

// /// Threading state through.  
// let thread s g (f1, x1) (f2, x2) =
//     let s', y1 = f1 s x1
//     let s'', y2 = f2 s' x2
//     g s'' (y1, y2)

// /// Perform an AND operation on BDDs, maintaining canonicity.
// let rec bdd_and (bdd,comp as bddcomp) (m1, m2) =
//     if m1 = -1 || m2 = -1 then bddcomp, -1
//     elif m1 = 1 then bddcomp, m2 
//     elif m2 = 1 then bddcomp, m1
//     else
//         try bddcomp, apply comp (m1, m2)
//         with Failure _ ->
//             try bddcomp, apply comp (m2, m1)
//             with Failure _ ->
//                 let p1, l1, r1 = expand_node bdd m1
//                 let p2, l2, r2 = expand_node bdd m2
//                 let p, lpair, rpair =
//                     if p1 = p2 then p1, (l1, l2), (r1, r2)
//                     elif order bdd p1 p2 then p1, (l1, m2), (r1, m2)
//                     else p2, (m1, l2), (m1, r2)
//                 let (bdd', comp'), (lnew, rnew) =
//                     thread bddcomp (fun s z -> s, z) (bdd_and, lpair) (bdd_and, rpair)
//                 let bdd'', n = mk_node bdd' (p, lnew, rnew)
//                 (bdd'', ((m1, m2) |-> n) comp'), n

// // ------------------------------------------------------------------------- //
// // The other binary connectives.                                             //
// // ------------------------------------------------------------------------- //

// let bdd_or bdc (m1, m2) = 
//     let bdc1, n = bdd_and bdc (-m1, -m2)
//     bdc1, -n

// let bdd_imp bdc (m1, m2) = 
//     bdd_or bdc (-m1, m2)

// let bdd_iff bdc (m1, m2) =
//     thread bdc bdd_or (bdd_and, (m1, m2)) (bdd_and, (-m1, -m2))

// /// Term to BDD conversion.  
// let rec mkbdd (bdd,comp as bddcomp) fm =
//     match fm with
//     | False _ ->
//         bddcomp, -1
//     | True _ ->
//         bddcomp, 1
//     | Atom s ->
//         let bdd', n = mk_node bdd (fm, 1, -1) 
//         (bdd', comp), n
//     | Not p ->
//         let bddcomp', n = mkbdd bddcomp p
//         bddcomp', -n
//     | And (p, q) ->
//         thread bddcomp bdd_and (mkbdd, p) (mkbdd, q)
//     | Or (p, q)  ->
//         thread bddcomp bdd_or (mkbdd, p) (mkbdd, q)
//     | Imp (p, q) ->
//         thread bddcomp bdd_imp (mkbdd, p) (mkbdd, q)
//     | Iff (p, q) ->
//         thread bddcomp bdd_iff (mkbdd, p) (mkbdd, q)
//     | _ -> failwith "mkbdd"

// let bddtaut fm = 
//     snd (mkbdd (mk_bdd (<), undefined) fm) = 1


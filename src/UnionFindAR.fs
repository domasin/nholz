/// Union-find algorithm.
/// 
/// The module is the porting of the union-find algorithm defined in the file 
/// lib.ml from the code that accompanies the book "handbook of practical logic 
/// and automated reasoning" (https://www.cl.cam.ac.uk/~jrh13/atp/) adapted to 
/// fit nholz HOL system.
/// 
/// Many of the implementations are based on the version of the code ported in 
/// F# by https://github.com/jack-pappas/fsharp-logic-examples/.
[<AutoOpen>]
module HOL.AutomatedReasoning.UnionFind

open HOL

// Type for use with union-find algorithm  
type pnode<'a> =
    | Nonterminal of 'a 
    | Terminal of 'a * int

/// Partition are equivalence relation on finite sets
type partition<'a> = 
    Partition of func<'a, pnode<'a>>

let rec string_of_partition par =
    let rec string_of_partition_interal par level =
        match par with
        | Partition x -> 
            let pt = string_of_patricia_tree_with_level x 1
            "Partition\n" + pt
    string_of_partition_interal par 0

let sprint_partition pt =
    string_of_partition pt

let print_partition pt =
    printfn "%O" (sprint_partition pt) |> ignore

let rec terminus (Partition f as ptn) a =
    match apply f a with
    | Terminal (p, q) ->
        p, q
    | Nonterminal b ->
        terminus ptn b

let tryterminus ptn a =
    try terminus ptn a
    with _ -> (a, 1)

/// Produces a canonical representative of the `ptn`-equivalence class 
/// containing `a`.
let canonize ptn a =
    fst <| tryterminus ptn a

/// Tests if `a` and `b` are equivalent w.r.t. `eqv`
let equivalent eqv a b =
    canonize eqv a = canonize eqv b

/// Produces a new partition that results from merging the `a` and `b` 
/// classes in `ptn`. I.e. the smallest equivalence relation containing `ptn` 
/// such that `a` and `b` are equivalent.
let equate (a, b) (Partition f as ptn) =
    let a', na = tryterminus ptn a
    let b', nb = tryterminus ptn b
    if a' = b' then f
    elif na <= nb then
        List.foldBack id [a' |-> Nonterminal b'; b' |-> Terminal (b', na + nb)] f
    else
        List.foldBack id [b' |-> Nonterminal a'; a' |-> Terminal (a', na + nb)] f
    |> Partition

/// An empty partition (equivalence class).
let unequal = 
    Partition undefined

/// the domain of the partition (equivalence class).
let equated (Partition f) = 
    dom f
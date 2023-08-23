/// Auxiliary set functions.
/// 
/// The module implements ideas described in the book "handbook of practical
/// logic and automated reasoning" (https://www.cl.cam.ac.uk/~jrh13/atp/)
/// adapting the code to fit nholz HOL system.
/// 
/// Many of the implementations are based on the version of the code ported in 
/// F# by https://github.com/jack-pappas/fsharp-logic-examples/.
[<AutoOpen>]
module HOL.AutomatedReasoning.SetOperations

open HOL

let subset'',psubset =
    let rec subset'' l1 l2 =
        match l1, l2 with
        | [], l2 -> true
        | l1, [] -> false
        | h1 :: t1, h2 :: t2 ->
            if h1 = h2 then subset'' t1 t2
            elif h1 < h2 then false
            else subset'' l1 t2
    /// Proper subset
    and psubset l1 l2 =
        match l1, l2 with
        | l1, [] -> false
        | [], l2 -> true
        | h1 :: t1, h2 :: t2 ->
            if h1 = h2 then psubset t1 t2
            elif h1 < h2 then false
            else subset'' l1 t2
    (fun s1 s2 -> subset'' (setify s1) (setify s2)),
    (fun s1 s2 -> psubset (setify s1) (setify s2))

// ------------------------------------------------------------------------- //
// Finding all subsets or all subsets of a given size.                       //
// ------------------------------------------------------------------------- //

// pg. 620
let rec allsets m l =
    if m = 0 then [[]]
    else
        match l with
        | [] -> []
        | h :: t ->
            union (image (fun g -> h :: g) (allsets (m - 1) t)) (allsets m t)
        
// pg. 620
let rec allsubsets s =
    match s with
    | [] -> [[]]
    | a :: t ->
        let res = allsubsets t
        union (image (fun b -> a :: b) res) res
                    
// pg. 620
let allnonemptysubsets s =
    subtract (allsubsets s) [[]]
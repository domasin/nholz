/// Auxiliary search functions.
/// 
/// The module implements ideas described in the book "handbook of practical
/// logic and automated reasoning" (https://www.cl.cam.ac.uk/~jrh13/atp/)
/// adapting the code to fit nholz HOL system.
/// 
/// Many of the implementations are based on the version of the code ported in 
/// F# by https://github.com/jack-pappas/fsharp-logic-examples/.
[<AutoOpen>]
module HOL.AutomatedReasoning.Search

open HOL

// ------------------------------------------------------------------------- //
// Find list member that maximizes or minimizes a function.                  //
// ------------------------------------------------------------------------- //

/// finds the element of a list l that maximizes or minimizes a function f 
/// based on the given ord.
/// 
/// Support function for use with maximize and minimize.
let optimize ord f lst =
    lst
    |> List.map (fun x -> x, f x)
    |> List.reduceBack (fun (_, y1 as p1) (_, y2 as p2) ->
        if ord y1 y2 then p1 else p2)
    |> fst
                        
/// finds the element of a list l that maximizes a function f
/// 
/// maximize ((*) -1) [-1;2;3] returns -1
let maximize f l =
    optimize (>) f l
    
/// finds the element of a list l that minimizes a function f
/// 
/// minimize ((*) -1) [-1;2;3] returns 3
let minimize f l =
    optimize (<) f l

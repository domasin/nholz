/// Some applications of the automated reasoning in the propositional fragments
/// 
/// The module implements ideas described in the book "handbook of practical
/// logic and automated reasoning" (https://www.cl.cam.ac.uk/~jrh13/atp/)
/// adapting the code to fit nholz HOL system.
/// 
/// Many of the implementations are based on the version of the code ported in 
/// F# by https://github.com/jack-pappas/fsharp-logic-examples/.
[<AutoOpen>]
module HOL.AutomatedReasoning.PropExamples

open HOL

/// Generate assertion equivalent to R(s,t) <= n for the Ramsey number R(s,t) 
let ramsey s t n =
    let vertices = [1..n]
    let yesgrps = List.map (allsets 2) (allsets s vertices)
    let nogrps = List.map (allsets 2) (allsets t vertices)
    let e = function 
        | [m;n] -> "p_" + (string m) + "_" + (string n) + ":bool" |> parse_term
        | _ -> failwith "unexpected input ramsey:e"
    mk_disj (
        list_disj (List.map (list_conj << List.map e) yesgrps),
        list_disj (List.map (list_conj << List.map (fun p -> mk_not (e p))) nogrps))
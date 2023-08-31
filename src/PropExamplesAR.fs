/// Some propositional formulas to test, and functions to generate classes.
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

// ========================================================================= //
// Ramsey Therorem                                                           //
// ========================================================================= //

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

// ========================================================================= //
// Addition of n-bit numbers as circuits or propositional terms              //
// ========================================================================= //

//     1 0 1 1 0 0 1 1
// +   0 1 1 0 0 1 0 1
// = 1 0 0 0 1 1 0 0 0

// ------------------------------------------------------------------------- //
// Half adder.                                                          
//
// An half adder (or 1-bit adder) calculates the sum and carry for just two 
// digits x and y to be added. 
// 
// x|y||c|s
// ---||---
// 0|0||0|0
// 0|1||0|1
// 1|0||0|1
// 1|1||1|0
// ------------------------------------------------------------------------- //

/// Generates the propositional term whose truth value correponds to the carry 
/// of an half adder, given the x and y digits to be summed also represented 
/// as terms: false for 0 true for 1.
/// 
/// x /\ y
let halfcarry x y = 
    mk_conj (x,y)

/// Generates the propositional term whose truth value correponds to the sum 
/// of an half adder, given the x and y digits to be summed also represented 
/// as terms: false for 0 true for 1. 
/// 
/// x <=> ~ y.
let halfsum x y = 
    mk_eq (x, mk_not y)

/// Half adder function.
/// 
/// Generates a propositional term that is true if the input terms represent 
/// respectively two digits x and y to be summed, the resulting sum s 
/// and the carry c.
let ha x y s c = 
    mk_conj (mk_eq (s, halfsum x y), mk_eq (c, halfcarry x y))

// ------------------------------------------------------------------------- //
// Full adder.
//
// A full adder (or n-bit adder) calculates the sum and carry for three digits 
// x, y and z where x and y are the digits to be summed and z is the carry 
// from a previous sum.
// 
// x|y|z||c|s
// -----||---
// 0|0|0||0|0
// 0|0|1||0|1
// 0|1|0||0|1
// 0|1|1||1|0
// 1|0|0||0|1
// 1|0|1||1|0
// 1|1|0||1|0
// 1|1|1||1|1
// ------------------------------------------------------------------------- //

/// Generates the propositional term whose truth value correponds to the carry 
/// of a full adder, given the x, y and z digits to be summed also represented 
/// as terms: false for 0 true for 1. 
/// 
/// (x /\ y) \/ ((x \/ y) /\ z)
let carry x y z = 
    mk_disj(mk_conj(x,y),mk_conj(mk_disj(x,y),z))

/// Generates the propositional term whose truth value correponds to the sum 
/// of a full adder, given the x, y and z digits to be summed also represented 
/// as terms: false for 0 true for 1. 
/// 
/// (x <=> ~ y) <=> ~ z
let sum x y z = 
    halfsum (halfsum x y) z

/// Full adder function.
/// 
/// Generates a propositional term that is true if the input terms represent 
/// respectively two digits x and y to be summed, the z carry from a previous 
/// sum, the resulting sum s and the carry c.
let fa x y z s c = 
    mk_conj(mk_eq(s,sum x y z),mk_eq(c,carry x y z))

// ------------------------------------------------------------------------- //
// Useful idiom.                                                             //
// ------------------------------------------------------------------------- //

let conjoin f l = list_conj (List.map f l)

// ------------------------------------------------------------------------- //
// n-bit ripple carry adder with carry c(0) propagated in and c(n) out.      //
// ------------------------------------------------------------------------- //

/// Generates a propsitional term that represent a riple-carry adder circuit.
/// 
/// Filtering the true rows of its truth table gives the sum and carry values 
/// for each digits.
let ripplecarry x y c out n =
    conjoin (fun i -> fa (x i) (y i) (c i) (out i) (c (i + 1)))
            ([0 .. (n - 1)])
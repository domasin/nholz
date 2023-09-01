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

(**********************************) 
(*          Addizione             *)
(**********************************) 

// Mezzo addizionatore (vale solo per la cifra più a destra 
// che non prevede andcora riporto)

let halfsum x y = mk_eq (x, mk_not y)
let halfcarry x y = mk_conj (x,y)

let ha x y s c = mk_conj (mk_eq (s, halfsum x y), mk_eq (c, halfcarry x y))

let to01 tm = 
    match tm with
    | False _ -> 0
    | True _ -> 1
    | _ -> failwith "unexpected input"

halfcarry true_tm true_tm

halfsum true_tm true_tm

ha true_tm true_tm false_tm true_tm

printfn "x|y|c|s"
printfn "-------"
for x in [false_tm;true_tm] do 
    for y in [false_tm;true_tm] do 
        for c in [false_tm;true_tm] do 
            for s in [false_tm;true_tm] do 
                if tautology(ha x y s c) then 
                    printfn "%i|%i|%i|%i" (x |> to01) (y |> to01) (c |> to01) (s |> to01)

// Addizionatore completo (somma tre cifre perché una è il possibile 
// riporto dalla somma precedente)

let carry x y z = mk_disj(mk_conj(x,y),mk_conj(mk_disj(x,y),z))

carry p q false_tm

let sum x y z = halfsum (halfsum x y) z

sum p q false_tm

let fa x y z s c = mk_conj(mk_eq(s,sum x y z),mk_eq(c,carry x y z))

printfn "x|y|z||c|s"
printfn "----------"
for x in [false_tm;true_tm] do 
    for y in [false_tm;true_tm] do 
        for z in [false_tm;true_tm] do 
            for c in [false_tm;true_tm] do 
                for s in [false_tm;true_tm] do 
                    if tautology(fa x y z s c) then 
                        printfn "%i|%i|%i||%i|%i" (x |> to01) (y |> to01) (z |> to01) (c |> to01) (s |> to01)

let conjoin f l = list_conj (List.map f l)

let ripplecarry x y c out n =
    conjoin (fun i -> fa (x i) (y i) (c i) (out i) (c (i + 1)))
            ([0 .. (n - 1)])

let mk_index x (i : int) = (x + "_" + (string i) + ":bool") |> parse_term

let [x; y; out; c] = map mk_index ["X"; "Y"; "OUT"; "C"]

let filtered_truthtable value tm =
    // [P "p"; P "q"; P "r"]
    let ats = atoms tm
    // 5 + 1 = length of false + length of space
    let width = List.foldBack (max << String.length << pname) ats 5 + 1
    let fixw s = s + String.replicate (width - String.length s) " "
    let truthstring p = fixw (if p then "true" else "false")
    let mk_row v =
        let lis = ats |> map (fun x -> 
            match x with
            | Tmconst ("true", Tycomp ("bool", [])) -> fixw "true"
            | Tmconst ("false", Tycomp ("bool", [])) -> fixw "false"
            | _ -> truthstring(v x)
            )
        if (eval v tm) = true then 
            let ans = truthstring (eval v tm)
            printf "%s" (List.foldBack (+) lis ("| " + ans))
            printfn ""
        true
    let seperator = String.replicate (width * (List.length ats) + 9) "-"
    printfn "%s" (List.foldBack (fun s t -> fixw(pname s) + t) ats "| formula")
    printfn "%s" seperator
    let _ = onallvaluations mk_row (fun x -> false) ats
    printfn "%s" seperator
    printfn ""
            
ripplecarry x y c out 2
|> filtered_truthtable true

// Each true row of the truth table gives the correct values.
// For example:
//
// OUT_0 X_0   Y_0   C_0   C_1   OUT_1 X_1   Y_1   C_2   | formula
// ---------------------------------------------------------------
// false false false false false false false false false | true 
//
// Can be read as:
// 
// Index | 2 | 1 | 0 |
// ------|---|---|----
// C     | 0 | 0 | 0 |
// X     |   | 0 | 0 |
// Y     |   | 0 | 0 |
// OUT   |   | 0 | 0 |
//
// the row 
//
// OUT_0 X_0   Y_0   C_0   C_1   OUT_1 X_1   Y_1   C_2   | formula
// ---------------------------------------------------------------
// false false true  true  true  false true  false true  | true 
// 
// Can be read as
//
// Index | 2 | 1 | 0 |
// ------|---|---|----
// C     | 1 | 1 | 1 |
// X     |   | 1 | 0 |
// Y     |   | 0 | 1 |
// OUT   |   | 0 | 0 |
// 
// Notice that here we have a carry also at index 0


// ------------------------------------------------------------------------- //
// Special case with 0 instead of c(0).                                      //
// ------------------------------------------------------------------------- //

let ripplecarry0 x y c out n =
    psimplify (ripplecarry x y (fun i -> if i = 0 then false_tm else c i) out n)

ripplecarry0 x y c out 2

// ------------------------------------------------------------------------- //
// Carry-select adder                                                        //
// ------------------------------------------------------------------------- //

let ripplecarry1 x y c out n =
    psimplify (ripplecarry x y (fun i -> if i = 0 then true_tm else c i) out n)

let mux sel in0 in1 = mk_disj (mk_conj (mk_not sel, in0), mk_conj (sel, in1))

let offset n x i = x (n + i)

let rec carryselect x y c0 c1 s0 s1 c s n k =
    let k' = min n k
    let fm =
        mk_conj (mk_conj (ripplecarry0 x y c0 s0 k', ripplecarry1 x y c1 s1 k'),
            mk_conj (mk_eq (c k', mux (c 0) (c0 k') (c1 k')),
                conjoin (fun i -> mk_eq (s i, mux (c 0) (s0 i) (s1 i)))
                    ([0 .. (k' - 1)])))
    if k' < k then fm else
        mk_conj (fm, carryselect
            (offset k x) (offset k y) (offset k c0) (offset k c1)
            (offset k s0) (offset k s1) (offset k c) (offset k s)
            (n - k) k)

let mk_adder_test n k =
    let l = List.map mk_index ["x"; "y"; "c"; "s"; "c0"; "s0"; "c1"; "s1"; "c2"; "s2"]
    match l with
    | [x; y; c; s; c0; s0; c1; s1; c2; s2] -> 
        mk_imp (mk_conj (mk_conj (carryselect x y c0 c1 s0 s1 c s n k, mk_not (c 0)), ripplecarry0 x y c2 s2 n), mk_conj (mk_eq (c n,c2 n), conjoin (fun i -> mk_eq (s i, s2 i)) [0 .. (n - 1)]))
    | _ -> failwith "mk_adder_test"

// tautology(mk_adder_test 1 1)
// tautology(mk_adder_test 2 1)

// ------------------------------------------------------------------------- //
// Primality examples.                                                       //
// For large examples, should use "num" instead of "int" in these functions. //
// ------------------------------------------------------------------------- //

let rec bitlength x = if x = 0 then 0 else 1 + bitlength (x / 2)

let rec bit n x = if n = 0 then x % 2 = 1 else bit (n - 1) (x / 2)

bit 0 2

/// Produces a term asserting that the atoms x(i) encode the bits of a value m, 
/// at least modulo 2^n.
let congruent_to x m n =
    [0 .. (n - 1)]
    |> conjoin (fun i -> 
        if bit i m then 
            x i 
        else 
            mk_not (x i)
        )
            

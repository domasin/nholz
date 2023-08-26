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
// che non prevede andcora priporto)

let halfsum x y = mk_eq (x, mk_not y)
let halfcarry x y = mk_conj (x,y)

let ha x y s c = mk_conj (mk_eq (s, halfsum x y), mk_eq (c, halfcarry x y))

let to01 tm = 
    match tm with
    | False _ -> 0
    | True _ -> 1
    | _ -> failwith "unexpected input"

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
let sum x y z = halfsum (halfsum x y) z
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

// ------------------------------------------------------------------------- //
// Useful idiom.                                                             //
// ------------------------------------------------------------------------- //

let conjoin f l = list_conj (List.map f l)
    
// pg. 67
// ------------------------------------------------------------------------- //
// n-bit ripple carry adder with carry c(0) propagated in and c(n) out.      //
// ------------------------------------------------------------------------- //

let ripplecarry x y c out n =
    conjoin (fun i -> fa (x i) (y i) (c i) (out i) (c (i + 1)))
            ([0 .. (n - 1)])

let mk_index x (i : int) = (x + "_" + (string i) + ":bool") |> parse_term

let mk_index2 x i j =
    (x + "_" + (string i) + "_" + (string j) + ":bool") |> parse_term

let [x; y; out; c] = map mk_index ["X"; "Y"; "OUT"; "C"]

@"((OUT_0 <=> ((X_0 <=> ~ Y_0) <=> ~ C_0)) /\
(C_1 <=> X_0 /\ Y_0 \/ (X_0 \/ Y_0) /\ C_0)) /\
(OUT_1 <=> ((X_1 <=> ~ Y_1) <=> ~C_1)) /\
(C_2 <=> X_1 /\ Y_1 \/ (X_1 \/ Y_1) /\ C_1)"
|> parse_term
|> tautology


let truthTable values fm =
    // [P "p"; P "q"; P "r"]
    let ats = atoms fm
    // 5 + 1 = length of false + length of space
    let width = List.foldBack (max << String.length << pname) ats 5 + 1
    let fixw s = s + String.replicate (width - String.length s) " "
    let truthstring p = fixw (if p then "1" else "0")
    let mk_row v =
        let lis = ats |> map (fun x -> 
            match x with
            | True _ -> fixw "1"
            | False _ -> fixw "0"
            | _ -> truthstring(v x)
            )
        if values |> List.contains (eval v fm) then 
            let ans = truthstring (eval v fm)
            printf "%s" (List.foldBack (+) lis ("| " + ans))
            printfn "" |> ignore
        true
    let seperator = String.replicate (width * (List.length ats) + 9) "-"
    printfn "%s" (List.foldBack (fun s t -> fixw(pname s) + t) ats "| formula")
    printfn "%s" seperator
    let _ = onallvaluations mk_row (fun x -> false) ats
    printfn "%s" seperator
    printfn ""

@"p /\ q /\ z"
|> parse_term
|> truthTable [true]

@"p /\ q /\ z"
|> parse_term
|> truthTable [true;false]

ripplecarry x y c out 2
|> truthTable [true]

// ------------------------------------------------------------------------- //
// Special case with 0 instead of c(0).                                      //
// ------------------------------------------------------------------------- //

let ats = @"p /\ q /\ z" |> parse_term |> atoms

let even x = x % 2 = 0

[0.0..(2. ** ats.Length)] 
|> List.chunkBySize 3

let ripplecarry0 x y c out n =
    psimplify (ripplecarry x y (fun i -> if i = 0 then false_tm else c i) out n)


ripplecarry0 x y c out 2
|> truthTable [true]


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
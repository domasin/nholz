#r "nuget: nholz2"

open HOL

fsi.AddPrinter print_type
fsi.AddPrinter print_qtype
fsi.AddPrinter print_term
fsi.AddPrinter print_qterm
fsi.AddPrinter print_thm

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

BoolClass.bool_cases_thm

fun_eq_thm

let latexStr (loc:Proof Location) =
    let (Loc(Tree((exp,_,_),_), _)) = loc
    let proof = loc |> root
    proof 
    |> treeToLatex 1 exp
    |> fun x -> x.Replace("\\color{green}", "")
    |> fun x -> x.Replace("\\textsf", "")
    |> fun x -> x.Replace("_", "\\_")

let x = parse_term(@"x:'a") 
let f = parse_term(@"f:'a->'b") 
let g = parse_term(@"g:'a->'b")

(* |- !f g. f = g <=> (!x. f x = g x) *)
(list_gen_rule_fd [f;g]
(deduct_antisym_rule_fd
    (* !x. f x = g x |- f = g                 *)
    (list_trans_rule_fd
        [ (*               |- f = (\x. f x)      *)
        sym_rule_fd (eta_conv_fd (parse_term(@"\x. (f:'a->'b) x")));
        (* !x. f x = g x |- ... = (\x. g x)    *)
        mk_abs_rule_fd x
            (spec_rule_fd x (assume_rule_fd (parse_term(@"!x. (f:'a->'b) x = g x"))));
        (*               |- ... = g            *)
        eta_conv_fd (parse_term(@"\x. (g:'a->'b) x")) ])
    (* f = g |- !x. f x = g x                 *)
    (gen_rule_fd x
    (mk_comb1_rule_fd (assume_rule_fd (parse_term(@"(f:'a->'b)=g"))) x) )))
|> zipper 
|> latexStr
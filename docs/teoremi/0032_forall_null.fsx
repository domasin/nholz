(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

forall_null_thm

let th = "t:bool" |> parse_term |> assume_rule
let th2 = gen_rule ("x:a" |> parse_term) th

([],"!t. (!(x:'a). t) <=> t")
|> start_proof
|> gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> gen_rule_bk
|> assume_rule_bk
|> spec_rule_bk ("x:a","x:a") "!(x:a). t"
|> assume_rule_bk
//|> view
|> root
|> linearizeProof


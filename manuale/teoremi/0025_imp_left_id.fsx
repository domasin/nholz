(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

imp_left_id_thm

([],"!p. true ==> p <=> p")
|> start_proof
|> gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> disch_rule_bk
|> add_asm_rule_bk 1
|> assume_rule_bk
|> mp_rule_bk [0] [] "true"
|> assume_rule_bk
|> by truth_thm "truth\_thm"
//|> view
|> root
|> linearizeProof

"(true ==> p) <=> p" |> parse_term |> dest_imp

([],"!p. true ==> (p <=> p)")
|> start_proof
|> gen_rule_bk
|> disch_rule_bk 
|> add_asm_rule_bk 0
|> refl_conv_bk

|> view
//|> root
//|> linearizeProof
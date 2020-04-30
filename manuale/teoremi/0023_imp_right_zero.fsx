(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

imp_right_zero_thm

([],"!p. p ==> true")
|> start_proof
|> gen_rule_bk
|> disch_rule_bk
|> add_asm_rule_bk 0
|> by truth_thm "truth_thm"

|> view


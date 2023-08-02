(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

imp_left_zero_thm

([],"!p. false ==> p")
|> start_proof
|> gen_rule_bk
|> disch_rule_bk
|> contr_rule_bk
|> assume_rule_bk

|> view
(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

imp_refl_thm

([],"!p. p ==> p")
|> start_proof
|> gen_rule_bk
|> disch_rule_bk
|> assume_rule_bk

|> view
(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_absorb_disj_thm
// |- !p q. p /\ (p \/ q) <=> p


([],"!p q. p /\ (p \/ q) <=> p")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> conj_rule_bk [0] [0]
|> assume_rule_bk
|> disj1_rule_bk
|> assume_rule_bk
|> conjunct1_rule_bk "p \/ q"
|> assume_rule_bk

|> view

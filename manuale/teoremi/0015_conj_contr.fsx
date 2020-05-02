(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_contr_thm

([],"!p. p /\ ~ p <=> false")
|> start_proof
|> gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> conj_rule_bk [0] [0]
|> contr_rule_bk
|> assume_rule_bk
|> contr_rule_bk
|> assume_rule_bk
|> mp_rule_bk [0] [0] "p:bool"
|> not_elim_rule_bk
|> conjunct2_rule_bk "p:bool"
|> assume_rule_bk
|> conjunct1_rule_bk "~ p"
|> assume_rule_bk

|> view


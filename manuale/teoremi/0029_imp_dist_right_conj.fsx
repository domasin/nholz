(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

imp_dist_right_conj_thm

([],"!p q r. (p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> disch_rule_bk
|> conj_rule_bk [0;1] [0;1]
|> undisch_rule_bk 1
|> conjunct1_rule_bk "p ==> r"
|> assume_rule_bk
|> undisch_rule_bk 1
|> conjunct2_rule_bk "p ==> q"
|> assume_rule_bk
|> conj_rule_bk [0] [0]
|> disch_rule_bk
|> conjunct1_rule_bk "r:bool"
|> undisch_rule_bk 1
|> assume_rule_bk
|> disch_rule_bk
|> conjunct2_rule_bk "q:bool"
|> undisch_rule_bk 1
|> assume_rule_bk

|> view
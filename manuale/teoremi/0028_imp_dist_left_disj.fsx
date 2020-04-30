(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

imp_dist_left_disj_thm

([],"!p q r. (p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> disch_rule_bk
|> disj_cases_rule_bk [1] [0] [0] "p:bool" "q:bool"
|> assume_rule_bk
|> mp_rule_bk [0] [1] "p:bool"
|> conjunct1_rule_bk "q ==> r"
|> assume_rule_bk
|> assume_rule_bk
|> mp_rule_bk [0] [1] "q:bool"
|> conjunct2_rule_bk "p ==> r"
|> assume_rule_bk
|> assume_rule_bk
|> conj_rule_bk [0] [0]
|> disch_rule_bk
|> mp_rule_bk [0] [1] "p \/ q"
|> assume_rule_bk
|> disj1_rule_bk
|> assume_rule_bk
|> disch_rule_bk
|> mp_rule_bk [0] [1] "p \/ q"
|> assume_rule_bk
|> disj2_rule_bk
|> assume_rule_bk

|> view
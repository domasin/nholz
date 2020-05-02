(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

disj_dist_right_conj_thm

([],"!p q r. p \/ (q /\ r) <=> (p \/ q) /\ (p \/ r)")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> disj_cases_rule_bk [0] [] [0] "p:bool" "q:bool"
|> conjunct1_rule_bk "p \/ r"
|> assume_rule_bk
|> disj1_rule_bk
|> assume_rule_bk
|> disj_cases_rule_bk [0] [] [1] "p:bool" "r:bool"
|> conjunct2_rule_bk "p \/ q"
|> assume_rule_bk
|> disj1_rule_bk
|> assume_rule_bk
|> disj2_rule_bk
|> conj_rule_bk [0] [1]
|> assume_rule_bk
|> assume_rule_bk
|> disj_cases_rule_bk [0] [] [] "p:bool" "q /\ r"
|> assume_rule_bk
|> conj_rule_bk [0] [0]
|> disj1_rule_bk
|> assume_rule_bk
|> disj1_rule_bk
|> assume_rule_bk
|> conj_rule_bk [0] [0]
|> disj2_rule_bk
|> conjunct1_rule_bk "r:bool"
|> assume_rule_bk
|> disj2_rule_bk
|> conjunct2_rule_bk "q:bool"
|> assume_rule_bk

|> view


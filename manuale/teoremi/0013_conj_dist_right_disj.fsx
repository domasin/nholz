(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_dist_right_disj_thm
//   |- !p q r. p /\ (q \/ r) <=> (p /\ q) \/ (p /\ r)


([],"!p q r. p /\ (q \/ r) <=> (p /\ q) \/ (p /\ r)")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> conj_rule_bk [0] [0]
|> disj_cases_rule_bk [0] [] [] "(p /\ q)" "(p /\ r)"
|> assume_rule_bk
|> conjunct1_rule_bk "q:bool"
|> assume_rule_bk
|> conjunct1_rule_bk "r:bool"
|> assume_rule_bk
|> disj_cases_rule_bk [0] [] [] "(p /\ q)" "(p /\ r)"
|> assume_rule_bk
|> disj1_rule_bk
|> conjunct2_rule_bk "p:bool"
|> assume_rule_bk
|> disj2_rule_bk
|> conjunct2_rule_bk "p:bool"
|> assume_rule_bk
|> disj_cases_rule_bk [0] [0] [0] "q:bool" "r:bool"
|> conjunct2_rule_bk "p:bool"
|> assume_rule_bk

|> disj1_rule_bk
|> conj_rule_bk [0] [1]
|> conjunct1_rule_bk "q \/ r"
|> assume_rule_bk
|> assume_rule_bk

|> disj2_rule_bk
|> conj_rule_bk [0] [1]
|> conjunct1_rule_bk "q \/ r"
|> assume_rule_bk
|> assume_rule_bk


|> view

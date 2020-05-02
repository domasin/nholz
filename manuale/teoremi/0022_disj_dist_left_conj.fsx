(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

disj_dist_left_conj_thm

([],"!p q r. (p /\ q) \/ r <=> (p \/ r) /\ (q \/ r)")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []

|> disj_cases_rule_bk [0] [0] [0] "p:bool" "r:bool"
|> focus_goal
|> disj_cases_rule_bk [0] [0] [0] "q:bool" "r:bool"

|> conjunct2_rule_bk "p \/ r"
|> assume_rule_bk
|> add_asm_rule_bk 1

|> view


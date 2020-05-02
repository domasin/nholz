(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

disj_absorb_conj_thm

([],"!p q. p \/ (p /\ q) <=> p")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> disj1_rule_bk 
|> assume_rule_bk
|> disj_cases_rule_bk [0] [] [] "p:bool" "p /\ q"
|> assume_rule_bk
|> assume_rule_bk
|> conjunct1_rule_bk "q:bool"
|> assume_rule_bk

|> view


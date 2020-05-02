(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

disj_assoc_thm

([],"!p q r. p \/ (q \/ r) <=> (p \/ q) \/ r")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> disj_cases_rule_bk [0] [] [] "(p \/ q)" "r:bool"
|> assume_rule_bk
|> disj_cases_rule_bk [0] [] [] "p:bool" "q:bool"
|> assume_rule_bk
|> disj1_rule_bk 
|> assume_rule_bk
|> disj2_rule_bk 
|> disj1_rule_bk 
|> assume_rule_bk
|> disj2_rule_bk 
|> disj2_rule_bk 
|> assume_rule_bk
|> disj_cases_rule_bk [0] [] [] "p:bool" "q \/ r"
|> assume_rule_bk
|> disj1_rule_bk 
|> disj1_rule_bk 
|> assume_rule_bk
|> disj_cases_rule_bk [0] [] [] "q:bool" "r:bool"
|> assume_rule_bk
|> disj1_rule_bk 
|> disj2_rule_bk 
|> assume_rule_bk
|> disj2_rule_bk 
|> assume_rule_bk
//|> view
|> loc_thm |> Option.get


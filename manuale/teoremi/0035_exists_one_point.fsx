(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

exists_one_point_thm

([],"!P Q. (?(x:a). P x \/ Q x) <=> (?x. P x) \/ (?x. Q x)")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> disj_cases_rule_bk [0] [] [] "?(x:a). P x" "?(x:a). Q x"
|> assume_rule_bk
|> choose_rule_bk [0] [] 0 ("x:a","x:a")
|> assume_rule_bk
|> exists_rule_bk "x:a"
|> disj1_rule_bk
|> assume_rule_bk
|> choose_rule_bk [0] [] 0 ("x:a","x:a")
|> assume_rule_bk
|> exists_rule_bk "x:a"
|> disj2_rule_bk
|> assume_rule_bk
|> choose_rule_bk [0] [] 0 ("x:a","x:a")
|> assume_rule_bk
//|> focus_goal
|> disj_cases_rule_bk [0] [] [] "(P:a->bool) x" "(Q:a->bool) x"
|> assume_rule_bk
|> disj1_rule_bk
|> exists_rule_bk "x:a"
|> assume_rule_bk
|> disj2_rule_bk
|> exists_rule_bk "x:a"
|> assume_rule_bk
|> view
|> root
|> linearizeProof


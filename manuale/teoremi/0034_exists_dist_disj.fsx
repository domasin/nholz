(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

exists_dist_disj_thm

([],"!P a. (?(x:a). x = a /\ P x) <=> P a")
|> start_proof
|> gen_rule_bk
|> gen_rule_bk
|> deduct_antisym_rule_bk [] []

|> exists_rule_bk "a:a"
|> conj_rule_bk [] [0]
|> refl_conv_bk
|> assume_rule_bk
|> focus_goal
|> choose_rule_bk [0] [] 0 ("a:a","x:a")
|> exists_rule_bk "a:a"
|> conj_rule_bk [] [0]
|> refl_conv_bk

|> view


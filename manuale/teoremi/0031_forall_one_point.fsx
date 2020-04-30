(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

forall_one_point_thm

([],"!P a. (!x. x = a ==> P x) <=> P a")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> gen_rule_bk
|> disch_rule_bk
|> eq_mp_rule_bk [1] [0] "(P:1 -> bool) a"
|> sym_rule_bk
|> mk_comb2_rule_bk
|> assume_rule_bk
|> assume_rule_bk
|> mp_rule_bk [0] [] "(a:1) = a"
|> spec_rule_bk ("a:1","x:1") "!(x:1). x = a ==> P x"
|> assume_rule_bk
|> refl_conv_bk
|> view
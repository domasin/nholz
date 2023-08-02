(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

forall_dist_conj_thm

([],"!P Q. (!x. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> gen_rule_bk
|> conj_rule_bk [0] [0]
|> spec_rule_bk ("x:1","x:1")
|> conjunct1_rule_bk "!(x:1). Q x"
|> assume_rule_bk
|> spec_rule_bk ("x:1","x:1")
|> conjunct2_rule_bk "!(x:1). P x"
|> assume_rule_bk
|> conj_rule_bk [0] [0]
|> gen_rule_bk
|> conjunct1_rule_bk "(Q:1 -> bool) (x:1)"
|> spec_rule_bk ("x:1","x:1")
|> assume_rule_bk
|> gen_rule_bk
|> conjunct2_rule_bk "(P:1 -> bool) (x:1)"
|> spec_rule_bk ("x:1","x:1")
|> assume_rule_bk

|> view
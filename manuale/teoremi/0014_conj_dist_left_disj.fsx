(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_dist_left_disj_thm
//   |- !p q r. (p \/ q) /\ r <=> (p /\ r) \/ (q /\ r)


([],"!p q r. (p \/ q) /\ r <=> (p /\ r) \/ (q /\ r)")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []

|> view

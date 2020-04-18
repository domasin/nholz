(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_assoc_thm
//   |- !p q r. p /\ (q /\ r) <=> (p /\ q) /\ r


([],"!p q r. p /\ (q /\ r) <=> (p /\ q) /\ r")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> conj_rule_bk [0] [0]
|> conjunct1_rule_bk "q:bool"
|> conjunct1_rule_bk "r:bool"
|> assume_rule_bk
|> conj_rule_bk [0] [0]
|> conjunct2_rule_bk "p:bool"
|> conjunct1_rule_bk "r:bool"
|> assume_rule_bk
|> conjunct2_rule_bk @"p /\ q"
|> assume_rule_bk
//|> focus_goal
|> conj_rule_bk [0] [0]
|> conj_rule_bk [0] [0]
|> conjunct1_rule_bk @"q /\ r"
|> assume_rule_bk
|> conjunct1_rule_bk @"r:bool"
|> conjunct2_rule_bk @"p:bool"
|> assume_rule_bk
|> conjunct2_rule_bk @"q:bool"
|> conjunct2_rule_bk @"p:bool"
|> assume_rule_bk

|> view

let th1 = disj_cases_rule_fd                     (* p \/ q |- q \/ p      *)
            (assume_rule_fd (parse_term(@"p \/ q")))
            (disj2_rule_fd q (assume_rule_fd p))
            (disj1_rule_fd (assume_rule_fd q) p) in
let th2 = inst_rule_fd [(p,q);(q,p)] th1 in      (* q \/ p |- p \/ q      *)
list_gen_rule_fd [p;q]
  (deduct_antisym_rule_fd th2 th1)
|> zipper
|> view
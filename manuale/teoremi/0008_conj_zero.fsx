(**
congiunzione zero
=============

$\forall p.\ p \wedge \bot \Leftrightarrow \bot$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_zero_thm
//   |- !p. p /\ false <=> false

(**
Backward proof with tree
*)

([],"!p. p /\ false <=> false")
|> start_proof
|> gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> contr_rule_bk
|> assume_rule_bk
|> conjunct2_rule_bk "p:bool"
|> assume_rule_bk
|> view

(**
$

$
*)

gen_rule_fd p
    (deduct_antisym_rule_fd
      (contr_rule_fd (parse_term(@"p /\ false")) (assume_rule_fd false_tm))
      (conjunct2_rule_fd (assume_rule_fd (parse_term(@"p /\ false")))) )
|> zipper
|> view
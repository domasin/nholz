(**
congiunzione della stessa proposizione
=============

$\forall p.\ p \wedge p \Leftrightarrow p$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_idem_thm
//   |- !p. p /\ p <=> p

([],"!p. p /\ p <=> p")
|> start_proof
|> gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> conj_rule_bk [0] [0]
|> assume_rule_bk
|> assume_rule_bk
|> conjunct1_rule_bk "p:bool"
|> assume_rule_bk

|> view


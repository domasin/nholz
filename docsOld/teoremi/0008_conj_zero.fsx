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
\small{ 	\color{green}{\dfrac
	{p:bool
	\qquad
	\color{green}{\dfrac
		{\color{green}{\dfrac
			{p\ \wedge\ \bot
			\qquad
			\color{green}{\dfrac
				{\bot}
				{\bot\ \vdash\ \bot}
				\textsf{ assume_rule}}}
			{\bot\ \vdash\ p\ \wedge\ \bot}
			\textsf{ contr_rule}}
		\qquad
		\color{green}{\dfrac
			{\color{green}{\dfrac
				{p\ \wedge\ \bot}
				{p\ \wedge\ \bot\ \vdash\ p\ \wedge\ \bot}
				\textsf{ assume_rule}}}
			{p\ \wedge\ \bot\ \vdash\ \bot}
			\textsf{ conjunct2_rule}}}
		{\vdash\ p\ \wedge\ \bot\ \Leftrightarrow\ \bot}
		\textsf{ deduct_antisym_rule}}}
	{\vdash\ \forall\ p.\ p\ \wedge\ \bot\ \Leftrightarrow\ \bot}
	\textsf{ gen_rule}} }
$
*)

(**
Forward proof with tree
*)

gen_rule_fd p
    (deduct_antisym_rule_fd
      (contr_rule_fd (parse_term(@"p /\ false")) (assume_rule_fd false_tm))
      (conjunct2_rule_fd (assume_rule_fd (parse_term(@"p /\ false")))) )
|> zipper
|> view

(**
Classic forward proof without tree
*)

gen_rule p
    (deduct_antisym_rule
      (contr_rule (parse_term(@"p /\ false")) (assume_rule false_tm))
      (conjunct2_rule (assume_rule (parse_term(@"p /\ false")))) )
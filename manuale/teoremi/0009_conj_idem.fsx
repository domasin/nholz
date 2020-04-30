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

(**
Backward proof with tree
*)

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

(**
$
\small{ 	\color{green}{\dfrac
	{p:bool
	\qquad
	\color{green}{\dfrac
		{\color{green}{\dfrac
			{\color{green}{\dfrac
				{p:bool}
				{p\ \vdash\ p}
				\textsf{ assume_rule}}
			\qquad
			\color{green}{\dfrac
				{p:bool}
				{p\ \vdash\ p}
				\textsf{ assume_rule}}}
			{p\ \vdash\ p\ \wedge\ p}
			\textsf{ conj_rule}}
		\qquad
		\color{green}{\dfrac
			{\color{green}{\dfrac
				{p\ \wedge\ p}
				{p\ \wedge\ p\ \vdash\ p\ \wedge\ p}
				\textsf{ assume_rule}}}
			{p\ \wedge\ p\ \vdash\ p}
			\textsf{ conjunct1_rule}}}
		{\vdash\ p\ \wedge\ p\ \Leftrightarrow\ p}
		\textsf{ deduct_antisym_rule}}}
	{\vdash\ \forall\ p.\ p\ \wedge\ p\ \Leftrightarrow\ p}
	\textsf{ gen_rule}} }
$
*)

(**
Forward proof with tree
*)

gen_rule_fd p
    (deduct_antisym_rule_fd
      (conj_rule_fd (assume_rule_fd p) (assume_rule_fd p))
      (conjunct1_rule_fd (assume_rule_fd (parse_term(@"p /\ p")))) )
|> zipper
|> view

(**
Classic forward proof without tree
*)

gen_rule p
(deduct_antisym_rule
  (conj_rule (assume_rule p) (assume_rule p))
  (conjunct1_rule (assume_rule (parse_term(@"p /\ p")))) )
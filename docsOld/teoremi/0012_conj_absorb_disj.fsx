(**
assorbimento della disgiunzione nella congiunzione
=====================

$\forall p\ q.\ p \wedge (p \vee q) \Leftrightarrow p$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_absorb_disj_thm
// |- !p q. p /\ (p \/ q) <=> p

(**
Backward proof with tree
*)

([],"!p q. p /\ (p \/ q) <=> p")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> conj_rule_bk [0] [0]
|> assume_rule_bk
|> disj1_rule_bk
|> assume_rule_bk
|> conjunct1_rule_bk "p \/ q"
|> assume_rule_bk
|> view

(**
$
\small{ 	\color{green}{\dfrac
	{[p:bool;q:bool]
	\qquad
	\color{green}{\dfrac
		{\color{green}{\dfrac
			{\color{green}{\dfrac
				{p:bool}
				{p\ \vdash\ p}
				\textsf{ assume_rule}}
			\qquad
			\color{green}{\dfrac
				{\color{green}{\dfrac
					{p:bool}
					{p\ \vdash\ p}
					\textsf{ assume_rule}}
				\qquad
				q:bool}
				{p\ \vdash\ p\ \vee\ q}
				\textsf{ disj1_rule}}}
			{p\ \vdash\ p\ \wedge\ (p\ \vee\ q)}
			\textsf{ conj_rule}}
		\qquad
		\color{green}{\dfrac
			{\color{green}{\dfrac
				{p\ \wedge\ (p\ \vee\ q)}
				{p\ \wedge\ (p\ \vee\ q)\ \vdash\ p\ \wedge\ (p\ \vee\ q)}
				\textsf{ assume_rule}}}
			{p\ \wedge\ (p\ \vee\ q)\ \vdash\ p}
			\textsf{ conjunct1_rule}}}
		{\vdash\ p\ \wedge\ (p\ \vee\ q)\ \Leftrightarrow\ p}
		\textsf{ deduct_antisym_rule}}}
	{\vdash\ \forall\ p\ q.\ p\ \wedge\ (p\ \vee\ q)\ \Leftrightarrow\ p}
	\textsf{ list_gen_rule}} }
$
*)

(**
Forward proof with tree
*)

let th1 = assume_rule_fd p
list_gen_rule_fd [p;q]
  (deduct_antisym_rule_fd
    (conj_rule_fd th1 (disj1_rule_fd th1 q))
    (conjunct1_rule_fd (assume_rule_fd (parse_term(@"p /\ (p \/ q)")))) )
|> zipper
|> view

(**
Classic forward proof without tree
*)

let th1' = assume_rule p in
list_gen_rule [p;q]
  (deduct_antisym_rule
    (conj_rule th1' (disj1_rule th1' q))
    (conjunct1_rule (assume_rule (parse_term(@"p /\ (p \/ q)")))) )
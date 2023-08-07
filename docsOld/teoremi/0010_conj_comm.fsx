(**
Propriet&agrave; commutatativa della congiuzione
=============

$\forall p\ q.\ p \wedge q \Leftrightarrow q \wedge p$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_comm_thm
//   |- !p q. p /\ q <=> q /\ p

(**
Backward proof with tree
*)

([],"!p q. p /\ q <=> q /\ p")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> conj_rule_bk [0] [0] 
|> conjunct2_rule_bk "q:bool"
|> assume_rule_bk
|> conjunct1_rule_bk "p:bool"
|> assume_rule_bk
|> conj_rule_bk [0] [0] 
|> conjunct2_rule_bk "p:bool"
|> assume_rule_bk
|> conjunct1_rule_bk "q:bool"
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
				{\color{green}{\dfrac
					{q\ \wedge\ p}
					{q\ \wedge\ p\ \vdash\ q\ \wedge\ p}
					\textsf{ assume_rule}}}
				{q\ \wedge\ p\ \vdash\ p}
				\textsf{ conjunct2_rule}}
			\qquad
			\color{green}{\dfrac
				{\color{green}{\dfrac
					{q\ \wedge\ p}
					{q\ \wedge\ p\ \vdash\ q\ \wedge\ p}
					\textsf{ assume_rule}}}
				{q\ \wedge\ p\ \vdash\ q}
				\textsf{ conjunct1_rule}}}
			{q\ \wedge\ p\ \vdash\ p\ \wedge\ q}
			\textsf{ conj_rule}}
		\qquad
		\color{green}{\dfrac
			{\color{green}{\dfrac
				{\color{green}{\dfrac
					{p\ \wedge\ q}
					{p\ \wedge\ q\ \vdash\ p\ \wedge\ q}
					\textsf{ assume_rule}}}
				{p\ \wedge\ q\ \vdash\ q}
				\textsf{ conjunct2_rule}}
			\qquad
			\color{green}{\dfrac
				{\color{green}{\dfrac
					{p\ \wedge\ q}
					{p\ \wedge\ q\ \vdash\ p\ \wedge\ q}
					\textsf{ assume_rule}}}
				{p\ \wedge\ q\ \vdash\ p}
				\textsf{ conjunct1_rule}}}
			{p\ \wedge\ q\ \vdash\ q\ \wedge\ p}
			\textsf{ conj_rule}}}
		{\vdash\ p\ \wedge\ q\ \Leftrightarrow\ q\ \wedge\ p}
		\textsf{ deduct_antisym_rule}}}
	{\vdash\ \forall\ p\ q.\ p\ \wedge\ q\ \Leftrightarrow\ q\ \wedge\ p}
	\textsf{ list_gen_rule}} }
$
*)

(**
Forward proof with tree
*)

list_gen_rule_fd [p;q]
  (deduct_antisym_rule_fd 
    (inst_rule_fd [(p,q);(q,p)] 
        (conj_rule_fd                       (* p /\ q |- q /\ p      *)
            (conjunct2_rule_fd (assume_rule_fd (parse_term(@"p /\ q"))))
            (conjunct1_rule_fd (assume_rule_fd (parse_term(@"p /\ q")))))) 
    (conj_rule_fd                           (* p /\ q |- q /\ p      *)
        (conjunct2_rule_fd (assume_rule_fd (parse_term(@"p /\ q"))))
        (conjunct1_rule_fd (assume_rule_fd (parse_term(@"p /\ q"))))))
|> zipper
|> view

(**
Internal forward proof without tree
*)

let th1 = assume_rule (parse_term(@"p /\ q")) in
let th2 = conj_rule                           (* p /\ q |- q /\ p      *)
            (conjunct2_rule th1)
            (conjunct1_rule th1) in
let th3 = inst_rule [(p,q);(q,p)] th2 in      (* q /\ p |- p /\ q      *)
list_gen_rule [p;q]
  (deduct_antisym_rule th3 th2)
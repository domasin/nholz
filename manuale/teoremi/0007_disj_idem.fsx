(**
Disj Idem
=============

$\vdash \forall p.\ p \vee p \Leftrightarrow p$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

disj_idem_thm
// |- !p. p \/ p <=> p

let p = "p:bool" |> parse_term
let th1 = assume_rule p                                  //      p |- p
let th2 = disj1_rule th1 p                               //      p |- p \/ p
let th3 = assume_rule (@"p \/ p" |> parse_term)          // p \/ p |- p \/ p
let th4 = disj_cases_rule th3 th1 th1                    // p \/ p |- p
let th7 = deduct_antisym_rule th2 th4                    //        |- p \/ p <=> p
let th8 = gen_rule p th7                                 //        |- !p. p \/ p <=> p

(***hide***)
//let th1 = assume_rule_tr p                          
//let th2 = disj1_rule_tr th1 p                       
//let th3 = assume_rule_tr (@"p \/ p" |> parse_term)  
//let th4 = disj_cases_rule_tr th3 th1 th1            
//let th7 = deduct_antisym_rule_tr th2 th4            
//let th8 = gen_rule_tr p th7                         
(***unhide***)

(**
$
\small{ 	
\dfrac
	{p:bool
	\qquad
	\dfrac
		{\dfrac
			{\dfrac
				{p:bool}
				{p\ \vdash\ p}
				\textsf{ assume_rule}
			\qquad
			p:bool}
			{p\ \vdash\ p\ \vee\ p}
			\textsf{ disj1_rule}
		\qquad
		\dfrac
			{\dfrac
				{p\ \vee\ p}
				{p\ \vee\ p\ \vdash\ p\ \vee\ p}
				\textsf{ assume_rule}
			\qquad
			\dfrac
				{p:bool}
				{p\ \vdash\ p}
				\textsf{ assume_rule}
			\qquad
			\dfrac
				{p:bool}
				{p\ \vdash\ p}
				\textsf{ assume_rule}}
			{p\ \vee\ p\ \vdash\ p}
			\textsf{ disj_cases_rule}}
		{\vdash\ p\ \vee\ p\ \Leftrightarrow\ p}
		\textsf{ deduct_antisym_rule}}
	{\vdash\ \forall\ p.\ p\ \vee\ p\ \Leftrightarrow\ p}
	\textsf{ gen_rule} }
$
*)

(**
Disj Zero
=============

$\vdash \forall p.\ p \vee \top \Leftrightarrow \top$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

disj_zero_thm
// |- !p. p \/ true <=> true

let p = "p:bool" |> parse_term
let th1 = disj2_rule p truth_thm                        // |- p \/ true
let th2 = eqt_intro_rule th1                            // |- p \/ true <=> true
let th3 = gen_rule p th2                                // |- !p. p \/ true <=> true

(***hide***)
//let truth_thm_gr = (truth_thm, mkGraph (Th truth_thm, "truth\_thm") [])
//let th1 = disj2_rule_tr p truth_thm_gr 
//let th2 = eqt_intro_rule_tr th1
//let th3 = gen_rule_tr p th2
(***unhide***)

(**
$
\small{ 	
\dfrac
	{p:bool
	\qquad
	\dfrac
		{\dfrac
			{p:bool
			\qquad
			\vdash\ \top\; \mathbf{ truth\_thm}}
			{\vdash\ p\ \vee\ \top}
			\textsf{ disj2_rule}}
		{\vdash\ p\ \vee\ \top\ \Leftrightarrow\ \top}
		\textsf{ eqt_intro_rule}}
	{\vdash\ \forall\ p.\ p\ \vee\ \top\ \Leftrightarrow\ \top}
	\textsf{ gen_rule} }
$
*)
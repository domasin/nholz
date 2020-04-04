(**
Non falso equivale a vero
=============

$\vdash \neg \bot \Leftrightarrow \top$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

not_false_thm
//   |- ~ false <=> true


let truth_thm_tr = (truth_thm, mkGraph (Th truth_thm, "truth\_thm") [])

let th = 
    (* |- ~ false <=> true         *)
    deduct_antisym_rule_tr
      (* |- ~ false            *)
      (not_intro_rule_tr (disch_rule_tr (parse_term(@"false")) (assume_rule_tr (parse_term(@"false")))))
      (* |- true               *)
      truth_thm_tr

(**
$
\small{ 	
\dfrac
	{\dfrac
		{\dfrac
			{\bot
			\qquad
			\dfrac
				{\bot}
				{\bot\ \vdash\ \bot}
				\textsf{ assume_rule}}
			{\vdash\ \bot\ \Rightarrow\ \bot}
			\textsf{ disch_rule}}
		{\vdash\ \neg\ \bot}
		\textsf{ not_intro_rule}
	\qquad
	\vdash\ \top\; \mathbf{ truth\_thm}}
	{\vdash\ \neg\ \bot\ \Leftrightarrow\ \top}
	\textsf{ deduct_antisym_rule} }
$
*)
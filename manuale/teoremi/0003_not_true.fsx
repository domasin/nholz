(**
Non vero equivale a falso
=============

$\vdash \neg \top \Leftrightarrow \bot$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

not_true_thm
//   |- ~ true <=> false


let truth_thm_tr = (truth_thm, mkGraph (Th truth_thm, "truth\_thm") [])

let th = 
    (* |- ~ true <=> false         *)
    deduct_antisym_rule_tr
        (* false |- ~ true             *)
        (contr_rule_tr (parse_term(@"~ true")) (assume_rule_tr (parse_term(@"false"))))
        (* ~ true |- false             *)
        (eq_mp_rule_tr
          (* ~ true |- true <=> false    *)
          (eqf_intro_rule_tr (assume_rule_tr (parse_term(@"~ true"))))
           truth_thm_tr )

(**
$
\small{ 	
\dfrac
	{\dfrac
		{\neg\ \top
		\qquad
		\dfrac
			{\bot}
			{\bot\ \vdash\ \bot}
			\textsf{ assume_rule}}
		{\bot\ \vdash\ \neg\ \top}
		\textsf{ contr_rule}
	\qquad
	\dfrac
		{\dfrac
			{\dfrac
				{\neg\ \top}
				{\neg\ \top\ \vdash\ \neg\ \top}
				\textsf{ assume_rule}}
			{\neg\ \top\ \vdash\ \top\ \Leftrightarrow\ \bot}
			\textsf{ eqf_intro_rule}
		\qquad
		\vdash\ \top\; \mathbf{ truth\_thm}}
		{\neg\ \top\ \vdash\ \bot}
		\textsf{ eq_mp_rule}}
	{\vdash\ \neg\ \top\ \Leftrightarrow\ \bot}
	\textsf{ deduct_antisym_rule} }
$
*)
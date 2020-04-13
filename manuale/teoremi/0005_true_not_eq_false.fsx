(**
Vero non equivale a falso
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

true_not_eq_false_thm
//   |- ~ (true <=> false)

(**

ATTENZIONE! Prima di rigenerare implementare eqt_introrule_bk e valutare l'altra dimostrazione

*)

([],"~ (true <=> false)")
|> start_proof
|> eqf_elim_rule_bk
|> deduct_antisym_rule_bk [] []
|> deduct_antisym_rule_bk [] ["false" |> parse_term]
|> add_asm_rule_bk 0
|> by truth_thm "truth\_thm"
|> add_asm_rule_bk 1
|> assume_rule_bk
|> eq_mp_rule_bk [0] [0] "true"
|> assume_rule_bk
|> add_asm_rule_bk 0
|> by truth_thm "truth\_thm"

|> view

let truth_thm_tr = (truth_thm, mkGraph (Th truth_thm, "truth\_thm") [])

let th = 
    eqf_elim_rule_tr
      (deduct_antisym_rule_tr
        (* false |- true <=> false         *)
        (sym_rule_tr (eqt_intro_rule_tr (assume_rule_tr (parse_term(@"false")))))
        (* true <=> false |- false         *)
        (eq_mp_rule_tr (assume_rule_tr (parse_term(@"true <=> false"))) truth_thm_tr) )

(**
$\small{ 	
\dfrac
	{\dfrac
		{\dfrac
			{\dfrac
				{\dfrac
					{\bot}
					{\bot\ \vdash\ \bot}
					\textsf{ assume_rule}}
				{\bot\ \vdash\ \bot\ \Leftrightarrow\ \top}
				\textsf{ eqt_intro_rule}}
			{\bot\ \vdash\ \top\ \Leftrightarrow\ \bot}
			\textsf{ sym_rule}
		\qquad
		\dfrac
			{\dfrac
				{\top\ \Leftrightarrow\ \bot}
				{\top\ \Leftrightarrow\ \bot\ \vdash\ \top\ \Leftrightarrow\ \bot}
				\textsf{ assume_rule}
			\qquad
			\vdash\ \top\; \mathbf{ truth\_thm}}
			{\top\ \Leftrightarrow\ \bot\ \vdash\ \bot}
			\textsf{ eq_mp_rule}}
		{\vdash\ (\top\ \Leftrightarrow\ \bot)\ \Leftrightarrow\ \bot}
		\textsf{ deduct_antisym_rule}}
	{\vdash\ \neg\ (\top\ \Leftrightarrow\ \bot)}
	\textsf{ eqf_elim_rule} }
$
*)
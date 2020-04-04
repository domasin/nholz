(**
vero &egrave; l'identit&agrave; della congiunzione
=============

$\forall p.\ p \wedge \top \Leftrightarrow p$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_id_thm
//   |- !p. p /\ true <=> p

let truth_thm_tr = (truth_thm, mkGraph (Th truth_thm, "truth\_thm") [])

let p = parse_term(@"p:bool")

let th = 
    gen_rule_tr p
        (deduct_antisym_rule_tr 
            (* p |- p /\ true *)
            (conj_rule_tr (p |> assume_rule_tr) truth_thm_tr)
            (* p /\ true |- p *)
            (conjunct1_rule_tr (@"p /\ true" |> parse_term |> assume_rule_tr))
        )

th |> print_graph

(**
$\small{ 	
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
			\vdash\ \top\; \mathbf{ truth\_thm}}
			{p\ \vdash\ p\ \wedge\ \top}
			\textsf{ conj_rule}
		\qquad
		\dfrac
			{\dfrac
				{p\ \wedge\ \top}
				{p\ \wedge\ \top\ \vdash\ p\ \wedge\ \top}
				\textsf{ assume_rule}}
			{p\ \wedge\ \top\ \vdash\ p}
			\textsf{ conjunct1_rule}}
		{\vdash\ p\ \wedge\ \top\ \Leftrightarrow\ p}
		\textsf{ deduct_antisym_rule}}
	{\vdash\ \forall\ p.\ p\ \wedge\ \top\ \Leftrightarrow\ p}
	\textsf{ gen_rule} }
$
*)
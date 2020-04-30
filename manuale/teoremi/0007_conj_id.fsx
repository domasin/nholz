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

(**
Backward proof with tree
*)

([],"!p. p /\ true <=> p")
|> start_proof
|> gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> conj_rule_bk [0] []
|> assume_rule_bk
|> by truth_thm "truth_thm"
|> conjunct1_rule_bk "true"
|> assume_rule_bk
|> view
|> loc_thm |> Option.get

//val it : thm = |- !p. p /\ true <=> p

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
			\dfrac
				{}
				{\vdash\ \top}
				\textsf{ truth_thm}}
			{p\ \vdash\ p\ \wedge\ \top}
			\textsf{ conj_rule}}
		\qquad
		\color{green}{\dfrac
			{\color{green}{\dfrac
				{p\ \wedge\ \top}
				{p\ \wedge\ \top\ \vdash\ p\ \wedge\ \top}
				\textsf{ assume_rule}}}
			{p\ \wedge\ \top\ \vdash\ p}
			\textsf{ conjunct1_rule}}}
		{\vdash\ p\ \wedge\ \top\ \Leftrightarrow\ p}
		\textsf{ deduct_antisym_rule}}}
	{\vdash\ \forall\ p.\ p\ \wedge\ \top\ \Leftrightarrow\ p}
	\textsf{ gen_rule}} }
$
*)

(**
Forward proof with tree
*)

gen_rule_fd p
    (deduct_antisym_rule_fd
        (* p |- p /\ true *)
        (conj_rule_fd (p |> assume_rule_fd) (truth_thm |> thm_fd "truth_thm"))
        (* p /\ true |- p *)
        (conjunct1_rule_fd (@"p /\ true" |> parse_term |> assume_rule_fd))
    )
|> zipper
|> view
|> loc_thm |> Option.get

//val it : thm = |- !p. p /\ true <=> p

(**
Classic forward proof without tree
*)

gen_rule p
    (deduct_antisym_rule
      (conj_rule (assume_rule p) truth_thm)
      (conjunct1_rule (assume_rule (parse_term(@"p /\ true")))) )

//val it : thm = |- !p. p /\ true <=> p

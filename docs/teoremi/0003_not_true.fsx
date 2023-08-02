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

(**
Backward proof with tree
*)

([],@"~ true <=> false")
|> start_proof
(* |- ~ true <=> false         *)
|> deduct_antisym_rule_bk [] []
    (* false |- ~ true             *)
    |> contr_rule_bk
        |> assume_rule_bk
    (* ~ true |- false             *)
    |> eq_mp_rule_bk [0] [] "true"
            (* ~ true |- true <=> false    *)
            |> eqf_intro_rule_bk
                |> assume_rule_bk
            (* |- true  *)
            |> by truth_thm "truth_thm"
|> view
|> loc_thm |> Option.get

//val it : thm = |- ~ true <=> false

(**
$
\small{ 	\color{green}{\dfrac
	{\color{green}{\dfrac
		{\neg\ \top
		\qquad
		\color{green}{\dfrac
			{\bot}
			{\bot\ \vdash\ \bot}
			\textsf{ assume_rule}}}
		{\bot\ \vdash\ \neg\ \top}
		\textsf{ contr_rule}}
	\qquad
	\color{green}{\dfrac
		{\color{green}{\dfrac
			{\color{green}{\dfrac
				{\neg\ \top}
				{\neg\ \top\ \vdash\ \neg\ \top}
				\textsf{ assume_rule}}}
			{\neg\ \top\ \vdash\ \top\ \Leftrightarrow\ \bot}
			\textsf{ eqf_intro_rule}}
		\qquad
		\dfrac
			{}
			{\vdash\ \top}
			\textsf{ truth_thm}}
		{\neg\ \top\ \vdash\ \bot}
		\textsf{ eq_mp_rule}}}
	{\vdash\ \neg\ \top\ \Leftrightarrow\ \bot}
	\textsf{ deduct_antisym_rule}} }
$
*)

(**
Forward proof with tree
*)

//(* |- ~ true <=> false         *)
deduct_antisym_rule_fd
    (* false |- ~ true             *)
    (contr_rule_fd (parse_term(@"~ true")) (assume_rule_fd (parse_term(@"false"))))
    (* ~ true |- false             *)
    (eq_mp_rule_fd
        (* ~ true |- true <=> false    *)
        (eqf_intro_rule_fd (assume_rule_fd (parse_term(@"~ true"))))
        (truth_thm |> thm_fd "truth\_thm") )
|> zipper |> view |> loc_thm |> Option.get

(**
Classic forward proof without tree
*)

//(* |- ~ true <=> false         *)
deduct_antisym_rule
  (* false |- ~ true             *)
  (contr_rule (parse_term(@"~ true")) (assume_rule (parse_term(@"false"))))
  (* ~ true |- false             *)
  (eq_mp_rule
    (* ~ true |- true <=> false    *)
    (eqf_intro_rule (assume_rule (parse_term(@"~ true"))))
    truth_thm )

//val it : thm = |- ~ true <=> false
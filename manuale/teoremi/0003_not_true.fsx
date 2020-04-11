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

([],@"~ true <=> false")                                    |> start_proof
(* |- ~ true <=> false         *)
|> deduct_antisym_rule_bk [] []
    (* false |- ~ true             *)
    |> contr_rule_bk                                        |> right
        |> assume_rule_bk                                   |> lower |> prove |> lower |> prove |> right
    (* ~ true |- false             *)
    |> eq_mp_rule_bk ("true" |> mkGoal [])
            (* ~ true |- true <=> false    *)
            |> eqf_intro_rule_bk
                |> assume_rule_bk                           |> lower |> prove |> lower |> prove |> right
            (* |- true  *)
            |> by truth_thm "truth\_thm"                    |> lower |> prove |> lower |> prove
|> view
|> loc_thm |> Option.get

//val it : thm = |- ~ true <=> false

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
	{\color{red}{\vdash\ \neg\ \top\ \Leftrightarrow\ \bot}}
	\textsf{ deduct_antisym_rule} }
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
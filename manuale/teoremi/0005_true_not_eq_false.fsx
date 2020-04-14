(**
Vero non equivale a falso
=============

$\vdash \neg (\top \Leftrightarrow \bot)$
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
Backward proof with tree
*)

([],"~ (true <=> false)")
|> start_proof
|> eqf_elim_rule_bk
    |> deduct_antisym_rule_bk [] []
        (* false |- true <=> false         *)
        |> sym_rule_bk
            |> eqt_intro_rule_bk
                |> assume_rule_bk
        (* true <=> false |- false         *)
        |> eq_mp_rule_bk [0] [] "true"
            |> assume_rule_bk
                //|> add_asm_rule_bk 0
            |> by truth_thm "truth\_thm"
|> view
|> loc_thm |> Option.get

//val it : thm = |- ~ (true <=> false)

(**
$
\small{ 	
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
	{\color{red}{\vdash\ \neg\ (\top\ \Leftrightarrow\ \bot)}}
	\textsf{ eqf_elim_rule} }
$
*)

(**
Forward proof with tree

*)

eqf_elim_rule_fd
    (deduct_antisym_rule_fd
      (* false |- true <=> false         *)
      (sym_rule_fd (eqt_intro_rule_fd (assume_rule_fd (parse_term(@"false")))))
      (* true <=> false |- false         *)
      (eq_mp_rule_fd (assume_rule_fd(parse_term(@"true <=> false"))) (truth_thm |> thm_fd "truth\_thm") ) )
|> zipper 
//|> view //equals backward version
|> loc_thm |> Option.get

//val it : thm = |- ~ (true <=> false)

(**
Classic forward proof without tree
*)
eqf_elim_rule
    (deduct_antisym_rule
        (* false |- true <=> false         *)
        (sym_rule (eqt_intro_rule (assume_rule (parse_term(@"false")))))
        (* true <=> false |- false         *)
        (eq_mp_rule (assume_rule (parse_term(@"true <=> false"))) truth_thm) )

//val it : thm = |- ~ (true <=> false)
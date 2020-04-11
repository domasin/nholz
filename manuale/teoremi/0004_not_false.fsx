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

(**
Backward proof with tree
*)

([],"~ false <=> true")
|> start_proof
|> deduct_antisym_rule_bk [] []
    |> add_asm_rule_bk ("true" |> parse_term)       |> right
        |> not_intro_rule_bk
            |> disch_rule_bk                        |> right
                |> assume_rule_bk                   |> lower |> prove |> lower |> prove |> lower |> prove |> lower |> prove |> right
|> add_asm_rule_bk ("~ false" |> parse_term)        |> right
    |> by truth_thm "truth\_thm"                    |> lower |> prove |> lower |> prove
|> view
|> loc_thm |> Option.get

//val it : thm = |- ~ false <=> true

(**
$
\small{ 	
\dfrac
	{\dfrac
		{\top
		\qquad
		\dfrac
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
			\textsf{ not_intro}}
		{\top\ \vdash\ \neg\ \bot}
		\textsf{ add_asm_rule}
	\qquad
	\dfrac
		{\neg\ \bot
		\qquad
		\vdash\ \top\; \mathbf{ truth\_thm}}
		{\neg\ \bot\ \vdash\ \top}
		\textsf{ add_asm_rule}}
	{\color{red}{\vdash\ \neg\ \bot\ \Leftrightarrow\ \top}}
	\textsf{ deduct_antisym_rule} }
$
*)

(**
Forward proof with tree

(slightly smaller since we apply `deduct_antisym_rule` without assumptions.)
*)

//(* |- ~ false <=> true         *)
deduct_antisym_rule_fd
  (* |- ~ false            *)
  (not_intro_rule_fd (disch_rule_fd (parse_term(@"false")) (assume_rule_fd (parse_term(@"false")))))
  (* |- true               *)
  (truth_thm |> thm_fd "truth\_thm")
|> zipper |> view |> loc_thm |> Option.get

//val it : thm = |- ~ false <=> true

(**
$
\small{ 	\dfrac
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
	{\color{red}{\vdash\ \neg\ \bot\ \Leftrightarrow\ \top}}
	\textsf{ deduct_antisym_rule} }
$
*)

(**
Classic forward proof without tree
*)

//(* |- ~ false <=> true         *)
deduct_antisym_rule
  (* |- ~ false            *)
  (not_intro_rule (disch_rule (parse_term(@"false")) (assume_rule (parse_term(@"false")))))
  (* |- true               *)
  truth_thm

//val it : thm = |- ~ false <=> true
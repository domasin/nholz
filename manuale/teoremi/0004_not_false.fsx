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
    |> add_asm_rule_bk 0
        |> not_intro_rule_bk
            |> disch_rule_bk
                |> assume_rule_bk
    |> add_asm_rule_bk 0        
        |> by truth_thm "truth_thm"
|> view
|> loc_thm |> Option.get

//val it : thm = |- ~ false <=> true

(**
$
\small{ 	\color{green}{\dfrac
	{\color{green}{\dfrac
		{\top
		\qquad
		\color{green}{\dfrac
			{\color{green}{\dfrac
				{\bot
				\qquad
				\color{green}{\dfrac
					{\bot}
					{\bot\ \vdash\ \bot}
					\textsf{ assume_rule}}}
				{\vdash\ \bot\ \Rightarrow\ \bot}
				\textsf{ disch_rule}}}
			{\vdash\ \neg\ \bot}
			\textsf{ not_intro_rule}}}
		{\top\ \vdash\ \neg\ \bot}
		\textsf{ add_asm_rule}}
	\qquad
	\color{green}{\dfrac
		{\neg\ \bot
		\qquad
		\dfrac
			{}
			{\vdash\ \top}
			\textsf{ truth_thm}}
		{\neg\ \bot\ \vdash\ \top}
		\textsf{ add_asm_rule}}}
	{\vdash\ \neg\ \bot\ \Leftrightarrow\ \top}
	\textsf{ deduct_antisym_rule}} }
$
*)

(**
Forward proof with tree

(`deduct_antisym_rule_fd` can be applied without assumptions.)
*)

//(* |- ~ false <=> true         *)
deduct_antisym_rule_fd
  (* |- ~ false            *)
  (not_intro_rule_fd (disch_rule_fd (parse_term(@"false")) (assume_rule_fd (parse_term(@"false")))))
  (* |- true               *)
  (truth_thm |> thm_fd "truth_thm")
|> zipper |> view |> loc_thm |> Option.get

//val it : thm = |- ~ false <=> true

(**
$
\small{ 	\color{green}{\dfrac
	{\color{green}{\dfrac
		{\color{green}{\dfrac
			{\bot
			\qquad
			\color{green}{\dfrac
				{\bot}
				{\bot\ \vdash\ \bot}
				\textsf{ assume_rule}}}
			{\vdash\ \bot\ \Rightarrow\ \bot}
			\textsf{ disch_rule}}}
		{\vdash\ \neg\ \bot}
		\textsf{ not_intro_rule}}
	\qquad
	\dfrac
		{}
		{\vdash\ \top}
		\textsf{ truth_thm}}
	{\vdash\ \neg\ \bot\ \Leftrightarrow\ \top}
	\textsf{ deduct_antisym_rule}} }
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
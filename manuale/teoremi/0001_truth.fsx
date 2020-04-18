(**
Vero
=============

$\vdash \top$
*)



(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

truth_thm
// |- true

(**
Backward proof with tree
*)

([],"true")
|> start_proof
(* |- true                        *)
|> eq_mp_rule_bk [] [] "(\(p:bool). p) = \p. p"
    (* |- (\p. p) = (\p. p) <=> true  *)
    |> sym_rule_bk
        (* |- true <=> (\(p:bool). p) = (\p. p) *)
        |> by true_def "true\_def"
    (* |- (\p. p) = (\p. p)           *)
    |> refl_conv_bk
|> view
|> loc_thm |> Option.get

// val it : thm = |- true

(**
$
\small{ 	\color{green}{\dfrac
	{\color{green}{\dfrac
		{\vdash\ \top\ \Leftrightarrow\ (\lambda\ (p:bool).\ p)\ =\ (\lambda\ p.\ p)\; \mathbf{ true\_def}}
		{\vdash\ (\lambda\ (p:bool).\ p)\ =\ (\lambda\ p.\ p)\ \Leftrightarrow\ \top}
		\textsf{ sym_rule}}
	\qquad
	\color{green}{\dfrac
		{\lambda\ (p:bool).\ p}
		{\vdash\ (\lambda\ (p:bool).\ p)\ =\ (\lambda\ p.\ p)}
		\textsf{ refl_conv}}}
	{\vdash\ \top}
	\textsf{ eq_mp_rule}} }
$
*)

(**
Forward proof with tree
*)

//(* |- true                        *)
eq_mp_rule_fd
    (* |- (\p. p) = (\p. p) <=> true  *)
    (sym_rule_fd (true_def |> thm_fd "true\_def"))
    (* |- (\p. p) = (\p. p)           *)
    (refl_conv_fd (parse_term(@"\(p:bool).p")))
|> zipper |> view |> loc_thm |> Option.get

//val it : thm = |- true

(**
Classic forward proof without tree
*)

//(* |- true                        *)
eq_mp_rule
    (* |- (\p. p) = (\p. p) <=> true  *)
    (sym_rule true_def)
    (* |- (\p. p) = (\p. p)           *)
    (refl_conv (parse_term(@"\(p:bool).p")))

// val it : thm = |- true

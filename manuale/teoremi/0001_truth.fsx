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

let true_def_tr = true_def, mkTree(Th true_def, "true\_def") []

let th = 
    (* |- true                        *)
    eq_mp_rule_tr
      (* |- (\p. p) = (\p. p) <=> true  *)
      (sym_rule_tr true_def_tr)
      (* |- (\p. p) = (\p. p)           *)
      (refl_conv_tr (parse_term(@"\(p:bool).p")))

th |> print_tree

(**
$
\small{ 	\dfrac
	{\dfrac
		{\vdash\ \top\ \Leftrightarrow\ (\lambda\ (p:bool).\ p)\ =\ (\lambda\ p.\ p)\; \mathbf{ true\_def}}
		{\vdash\ (\lambda\ (p:bool).\ p)\ =\ (\lambda\ p.\ p)\ \Leftrightarrow\ \top}
		\textsf{ sym_rule}
	\qquad
	\dfrac
		{\lambda\ (p:bool).\ p}
		{\vdash\ (\lambda\ (p:bool).\ p)\ =\ (\lambda\ p.\ p)}
		\textsf{ refl_conv}}
	{\vdash\ \top}
	\textsf{ eq_mp_rule} }
$
*)
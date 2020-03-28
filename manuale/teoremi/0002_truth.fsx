(**
Verit&agrave;
=============

$\vdash \top$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
(***unhide***)

truth_thm
// |- true

true_def                                            // |- true <=> (\(p:bool). p) = (\p. p)
let tt1 = sym_rule true_def                         // |- (\(p:bool). p) = (\p. p) <=> true
let tt2 = refl_conv (parse_term(@"\(p:bool).p"))    // |- (\(p:bool). p) = (\p. p)
let tt3 = eq_mp_rule tt1 tt2                        // |- true

(***hide***)
let th1 = sym_rule_tr (true_def, mkGraph (Th true_def, "true\_def") [])
let th2 = @"\(p:bool).p" |> parse_term |> refl_conv_tr
let th3 = eq_mp_rule_tr th1 th2
(***unhide***)

(**
$
\small{ 	\dfrac
	{\dfrac
		{\vdash\ \top\ \Leftrightarrow\ (\lambda\ (p:bool).\ p)\ =\ (\lambda\ p.\ p) (true\_def)}
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
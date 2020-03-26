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

(**
$\scriptsize{
\dfrac
    {
        \dfrac
            {\dfrac{}{\vdash \top \Leftrightarrow (\lambda(p:bool). p) = (\lambda p. p)}\textsf{true_def}}
            {\vdash (\lambda (p:bool).\ p) = (\lambda p. p) \Leftrightarrow \top}\textsf{sym_rule}
        \qquad
        \dfrac{}{\vdash (\lambda (p:bool).\ p) = (\lambda p. p)}\textsf{refl_conv}
    }
    {\vdash \top}\textsf{eq_mp_rule}
}$
*)
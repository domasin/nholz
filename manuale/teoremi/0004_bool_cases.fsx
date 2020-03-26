(**
Bool Cases
=============

$\vdash \forall p.\ (p \Leftrightarrow \top) \vee (p \Leftrightarrow \bot)$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
(***unhide***)

bool_cases_thm
// |- !p. (p <=> true) \/ (p <=> false)

let p = mk_var ("p",bool_ty)
let tm1 = spec_rule p excluded_middle_thm                   //     |- p \/ ~ p
let tm2 = eqt_intro_rule (assume_rule p)                    //   p |- p <=> true
let tm3 = disj1_rule tm2 (parse_term(@"p <=> false"))       //   p |- (p <=> true) \/ (p <=> false)
let tm4 = eqf_intro_rule (assume_rule (parse_term(@"~ p"))) // ~ p |- p <=> false
let tm5 = disj2_rule (parse_term(@"p <=> true")) tm4        // ~ p |- (p <=> true) \/ (p <=> false)
let tm = disj_cases_rule tm1 tm3 tm5                        //     |- (p <=> true) \/ (p <=> false)

(**

$\scriptsize{
\dfrac
    {
        \dfrac{}{\vdash p \vee \neg p}\textsf{excluded_middle_thm}
        \qquad
        p \vdash (p \leftrightarrow \top) \vee (p \leftrightarrow \bot)
        \qquad
        \neg p \vdash (p \leftrightarrow \top) \vee (p \leftrightarrow \bot)
    }
    {\vdash p \leftrightarrow \top \vee p \leftrightarrow \bot}\textsf{disj_cases_rule}
}$
*)
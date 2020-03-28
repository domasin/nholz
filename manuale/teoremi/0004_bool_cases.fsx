(**
Bool Cases
=============

$\vdash \forall p.\ (p \Leftrightarrow \top) \vee (p \Leftrightarrow \bot)$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
BoolAlg.load
BoolClass.load
(***unhide***)

bool_cases_thm
// |- !p. (p <=> true) \/ (p <=> false)

let p = mk_var ("p",bool_ty)
let tm1 = spec_rule p excluded_middle_thm                   //     |- p \/ ~ p
let tm2 = eqt_intro_rule (assume_rule p)                    //   p |- p <=> true
let tm3 = disj1_rule tm2 (parse_term(@"p <=> false"))       //   p |- (p <=> true) \/ (p <=> false)
let tm4 = eqf_intro_rule (assume_rule (parse_term(@"~ p"))) // ~ p |- p <=> false
let tm5 = disj2_rule (parse_term(@"p <=> true")) tm4        // ~ p |- (p <=> true) \/ (p <=> false)
let tm6 = disj_cases_rule tm1 tm3 tm5                       //     |- (p <=> true) \/ (p <=> false)
let tm7 = gen_rule p tm6

(***hide***)
let excluded_middle_thm_gr = (excluded_middle_thm, mkGraph (Th excluded_middle_thm, "excluded\_middle\_thm") [])
let th1 = spec_rule_tr p excluded_middle_thm_gr

//let eqt_intro_rule_tr (th1,g1) = 
//    let th = th1 |> eqt_intro_rule
//    (th, mkGraph (Th th,"eqt_intro_rule") [g1])

let th2 = eqt_intro_rule_tr (assume_rule_tr p)
let th3 = disj1_rule_tr th2 (parse_term(@"p <=> false"))

//let eqf_intro_rule_tr (th1,g1) = 
//    let th = th1 |> eqf_intro_rule
//    (th, mkGraph (Th th,"eqf_intro_rule") [g1])

let th4 = eqf_intro_rule_tr (assume_rule_tr (parse_term(@"~ p")))
let th5 = disj2_rule_tr (parse_term(@"p <=> true")) th4 
let th6 = disj_cases_rule_tr th1 th3 th5
let th7 = gen_rule_tr p th6

(***unhide***)

(**

$
\small{ 	\dfrac
	{p:bool
	\qquad
	\dfrac
		{\dfrac
			{p:bool
			\qquad
			\vdash\ \forall\ p.\ p\ \vee\ \neg\ p}
			{\vdash\ p\ \vee\ \neg\ p}
			\textsf{ spec_rule}
		\qquad
		\dfrac
			{\dfrac
				{\dfrac
					{p:bool}
					{p\ \vdash\ p}
					\textsf{ assume_rule}}
				{p\ \vdash\ p\ \Leftrightarrow\ \top}
				\textsf{ eqt_intro_rule}
			\qquad
			p\ \Leftrightarrow\ \bot}
			{p\ \vdash\ (p\ \Leftrightarrow\ \top)\ \vee\ (p\ \Leftrightarrow\ \bot)}
			\textsf{ disj1_rule}
		\qquad
		\dfrac
			{p\ \Leftrightarrow\ \top
			\qquad
			\dfrac
				{\dfrac
					{\neg\ p}
					{\neg\ p\ \vdash\ \neg\ p}
					\textsf{ assume_rule}}
				{\neg\ p\ \vdash\ p\ \Leftrightarrow\ \bot}
				\textsf{ eqf_intro_rule}}
			{\neg\ p\ \vdash\ (p\ \Leftrightarrow\ \top)\ \vee\ (p\ \Leftrightarrow\ \bot)}
			\textsf{ disj2_rule}}
		{\vdash\ (p\ \Leftrightarrow\ \top)\ \vee\ (p\ \Leftrightarrow\ \bot)}
		\textsf{ disj_cases_rule}}
	{\vdash\ \forall\ p.\ (p\ \Leftrightarrow\ \top)\ \vee\ (p\ \Leftrightarrow\ \bot)}
	\textsf{ gen_rule} }
$
*)
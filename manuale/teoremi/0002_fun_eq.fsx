(**
Equivalenza tra funzioni
=============

$\vdash \forall (f:\alpha \rightarrow \beta)\ g.\ f = g\ \Leftrightarrow\ (\forall x.\ f\ x = g\ x)$

L'euivalenza tra funzioni corrisponde all'equivalenza dei loro valori a parit&agrave; di argomento.
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

fun_eq_thm
// |- !(f:'a->'b) g. f = g <=> (!x. f x = g x)

let x = parse_term(@"x:'a") 
let f = parse_term(@"f:'a->'b")
let g = parse_term(@"g:'a->'b")

let th = 
    (* |- !f g. f = g <=> (!x. f x = g x) *)
    (list_gen_rule_tr [f;g]
      (deduct_antisym_rule_tr
        (* !x. f x = g x |- f = g                 *)
        (list_trans_rule_tr
           [ (*               |- f = (\x. f x)      *)
             sym_rule_tr (eta_conv_tr (parse_term(@"\x. (f:'a->'b) x")));
             (* !x. f x = g x |- ... = (\x. g x)    *)
             mk_abs_rule_tr x
               (spec_rule_tr x (assume_rule_tr (parse_term(@"!x. (f:'a->'b) x = g x"))));
             (*               |- ... = g            *)
             eta_conv_tr (parse_term(@"\x. (g:'a->'b) x")) ])
        (* f = g |- !x. f x = g x                 *)
        (gen_rule_tr x
          (mk_comb1_rule_tr (assume_rule_tr (parse_term(@"(f:'a->'b)=g"))) x) )))

th |> print_tree

(**
$
\small{ 	\dfrac
	{f:\alpha\rightarrow\beta
	\qquad
	g:\alpha\rightarrow\beta
	\qquad
	\dfrac
		{\dfrac
			{\dfrac
				{\dfrac
					{\lambda\ x.\ (f:\alpha\rightarrow\beta)\ x}
					{\vdash\ (\lambda\ x.\ (f:\alpha\rightarrow\beta)\ x)\ =\ f}
					\textsf{ eta_conv}}
				{\vdash\ (f:\alpha\rightarrow\beta)\ =\ (\lambda\ x.\ f\ x)}
				\textsf{ sym_rule}
			\qquad
			\dfrac
				{x:\alpha
				\qquad
				\dfrac
					{x:\alpha
					\qquad
					\dfrac
						{\forall\ x.\ f\ x\ =\ (g:\alpha\rightarrow\beta)\ x}
						{\forall\ x.\ f\ x\ =\ g\ x\ \vdash\ \forall\ x.\ f\ x\ =\ (g:\alpha\rightarrow\beta)\ x}
						\textsf{ assume_rule}}
					{\forall\ x.\ f\ x\ =\ g\ x\ \vdash\ f\ x\ =\ (g:\alpha\rightarrow\beta)\ x}
					\textsf{ spec_rule}}
				{\forall\ x.\ f\ x\ =\ g\ x\ \vdash\ (\lambda\ x.\ f\ x)\ =\ (\lambda\ x.\ (g:\alpha\rightarrow\beta)\ x)}
				\textsf{ mk_abs_rule}
			\qquad
			\dfrac
				{\lambda\ x.\ (g:\alpha\rightarrow\beta)\ x}
				{\vdash\ (\lambda\ x.\ (g:\alpha\rightarrow\beta)\ x)\ =\ g}
				\textsf{ eta_conv}}
			{\forall\ x.\ f\ x\ =\ g\ x\ \vdash\ f\ =\ (g:\alpha\rightarrow\beta)}
			\textsf{ list_trans_rule}
		\qquad
		\dfrac
			{x:\alpha
			\qquad
			\dfrac
				{\dfrac
					{f\ =\ (g:\alpha\rightarrow\beta)}
					{f\ =\ g\ \vdash\ f\ =\ (g:\alpha\rightarrow\beta)}
					\textsf{ assume_rule}
				\qquad
				x:\alpha}
				{f\ =\ g\ \vdash\ f\ x\ =\ (g:\alpha\rightarrow\beta)\ x}
				\textsf{ mk_comb1_rule}}
			{f\ =\ g\ \vdash\ \forall\ x.\ f\ x\ =\ (g:\alpha\rightarrow\beta)\ x}
			\textsf{ gen_rule}}
		{\vdash\ f\ =\ (g:\alpha\rightarrow\beta)\ \Leftrightarrow\ (\forall\ x.\ f\ x\ =\ g\ x)}
		\textsf{ deduct_antisym_rule}}
	{\vdash\ \forall\ (f:\alpha\rightarrow\beta)\ g.\ f\ =\ g\ \Leftrightarrow\ (\forall\ x.\ f\ x\ =\ g\ x)}
	\textsf{ list_gen_rule} }
$
*)

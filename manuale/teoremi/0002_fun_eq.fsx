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

(**
Backward proof with tree
*)

([],@"!(f:'a->'b) g. f = g <=> (!x. f x = g x)") 
|> start_proof
|> list_gen_rule_bk
    |> deduct_antisym_rule_bk [] []
        |> trans_rule_bk "(\x. (g:'a->'b) x)"
            |> trans_rule_bk "(\x. (f:'a->'b) x)"
                |> add_asm_rule_bk 0
                    |> sym_rule_bk
                    |> eta_conv_bk
                |> mk_abs_rule_bk
                    |> spec_rule_bk ("x:'a" |> parse_term)
                        |> assume_rule_bk
            |> add_asm_rule_bk 0
                |> eta_conv_bk
        |> gen_rule_bk
            |> mk_comb1_rule_bk
                |> assume_rule_bk
|> view
|> loc_thm |> Option.get

//val it : thm = |- !(f:'a->'b) g. f = g <=> (!x. f x = g x)

(**
$
\small{ 	
\dfrac
	{[f:\alpha\rightarrow\beta,g:\alpha\rightarrow\beta]
	\qquad
	\dfrac
		{\dfrac
			{\dfrac
				{\dfrac
					{\forall\ x.\ f\ x\ =\ (g:\alpha\rightarrow\beta)\ x
					\qquad
					\dfrac
						{\dfrac
							{\lambda\ x.\ (f:\alpha\rightarrow\beta)\ x}
							{\vdash\ (\lambda\ x.\ (f:\alpha\rightarrow\beta)\ x)\ =\ f}
							\textsf{ eta_conv}}
						{\vdash\ (f:\alpha\rightarrow\beta)\ =\ (\lambda\ x.\ f\ x)}
						\textsf{ sym_rule}}
					{\forall\ x.\ f\ x\ =\ (g:\alpha\rightarrow\beta)\ x\ \vdash\ f\ =\ (\lambda\ x.\ f\ x)}
					\textsf{ add_asm_rule}
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
					\textsf{ mk_abs_rule}}
				{\forall\ x.\ f\ x\ =\ g\ x\ \vdash\ f\ =\ (\lambda\ x.\ (g:\alpha\rightarrow\beta)\ x)}
				\textsf{ trans_rule}
			\qquad
			\dfrac
				{\forall\ x.\ f\ x\ =\ (g:\alpha\rightarrow\beta)\ x
				\qquad
				\dfrac
					{\lambda\ x.\ (g:\alpha\rightarrow\beta)\ x}
					{\vdash\ (\lambda\ x.\ (g:\alpha\rightarrow\beta)\ x)\ =\ g}
					\textsf{ eta_conv}}
				{\forall\ x.\ f\ x\ =\ g\ x\ \vdash\ (\lambda\ x.\ (g:\alpha\rightarrow\beta)\ x)\ =\ g}
				\textsf{ add_asm_rule}}
			{\forall\ x.\ f\ x\ =\ g\ x\ \vdash\ f\ =\ (g:\alpha\rightarrow\beta)}
			\textsf{ trans_rule}
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
	{\color{red}{\vdash\ \forall\ (f:\alpha\rightarrow\beta)\ g.\ f\ =\ g\ \Leftrightarrow\ (\forall\ x.\ f\ x\ =\ g\ x)}}
	\textsf{ list_gen_rule} }
$
*)

(**
Forward proof with tree

Slightly smaller since the use of `list_trans_rule_fd`
*)

let x = parse_term(@"x:'a") 
let f = parse_term(@"f:'a->'b")
let g = parse_term(@"g:'a->'b")

(* |- !f g. f = g <=> (!x. f x = g x) *)
(list_gen_rule_fd [f;g]
  (deduct_antisym_rule_fd
    (* !x. f x = g x |- f = g                 *)
    (list_trans_rule_fd
       [ (*               |- f = (\x. f x)      *)
         sym_rule_fd (eta_conv_fd (parse_term(@"\x. (f:'a->'b) x")));
         (* !x. f x = g x |- ... = (\x. g x)    *)
         mk_abs_rule_fd x
           (spec_rule_fd x (assume_rule_fd (parse_term(@"!x. (f:'a->'b) x = g x"))));
         (*               |- ... = g            *)
         eta_conv_fd (parse_term(@"\x. (g:'a->'b) x")) 
         ])
    (* f = g |- !x. f x = g x                 *)
    (gen_rule_fd x
      (mk_comb1_rule_fd (assume_rule_fd (parse_term(@"(f:'a->'b)=g"))) x) )))
|> zipper
|> view
|> loc_thm |> Option.get

//val it : thm = |- !(f:'a->'b) g. f = g <=> (!x. f x = g x)

(**
$
\small{ 	
\dfrac
	{[f:\alpha\rightarrow\beta,g:\alpha\rightarrow\beta]
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
	{\color{red}{\vdash\ \forall\ (f:\alpha\rightarrow\beta)\ g.\ f\ =\ g\ \Leftrightarrow\ (\forall\ x.\ f\ x\ =\ g\ x)}}
	\textsf{ list_gen_rule} }
$
*)

(**
Classic forward proof without tree
*)

//(* |- !f g. f = g <=> (!x. f x = g x) *)
(list_gen_rule [f;g]
  (deduct_antisym_rule
    (* !x. f x = g x |- f = g                 *)
    (list_trans_rule
       [ (*               |- f = (\x. f x)      *)
         sym_rule (eta_conv (parse_term(@"\x. (f:'a->'b) x")));
         (* !x. f x = g x |- ... = (\x. g x)    *)
         mk_abs_rule x
           (spec_rule x (assume_rule (parse_term(@"!x. (f:'a->'b) x = g x"))));
         (*               |- ... = g            *)
         eta_conv (parse_term(@"\x. (g:'a->'b) x")) ])
    (* f = g |- !x. f x = g x                 *)
    (gen_rule x
      (mk_comb1_rule (assume_rule (parse_term(@"(f:'a->'b)=g"))) x) )))

//val it : thm = |- !(f:'a->'b) g. f = g <=> (!x. f x = g x)
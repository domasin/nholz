(**
Funzioni equivalenti
=============

$\vdash \forall (f:\alpha \rightarrow \beta)\ g.\ f = g\ \Leftrightarrow\ (\forall x.\ f\ x = g\ x)$

L'euivalenza tra funzione corrisponde all'equivalenza dei loro valori a parit&agrave; di argomento.
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
(***unhide***)

let x = parse_term(@"x:'a") 
let f = parse_term(@"f:'a->'b")
let g = parse_term(@"g:'a->'b")

let th1 = parse_term(@"\x. (f:'a->'b) x") |> eta_conv  // 1                |- (\x. (f:'a->'b) x) = f                  
let th2 = sym_rule th1                                 // 2                |- (f:'a->'b) = (\x. f x)                  
let th3 = parse_term(@"!x. (f:'a->'b) x = g x") 
            |> assume_rule                             // 3  !x. f x = g x |- !x. f x = (g:'a->'b) x                  
let th4 = spec_rule x th3                              // 4  !x. f x = g x |- f x = (g:'a->'b) x                      
let th5 = mk_abs_rule x th4                            // 5  !x. f x = g x |- (\x. f x) = (\x. (g:'a->'b) x)          
let th6 = parse_term(@"\x. (g:'a->'b) x") |> eta_conv  // 6                |- (\x. (g:'a->'b) x) = g                  
let th7 = [th2; th5; th6] |> list_trans_rule           // 7  !x. f x = g x |- f = (g:'a->'b)                          
let th8 = parse_term(@"(f:'a->'b)=g") |> assume_rule   // 8          f = g |- f = (g:'a->'b)                          
let th9 = mk_comb1_rule th8 x                          // 9          f = g |- f x = (g:'a->'b) x                      
let th10 = gen_rule x th9                              // 10         f = g |- !x. f x = (g:'a->'b) x                  
let th11 = deduct_antisym_rule th7 th10                // 11               |- f = (g:'a->'b) <=> (!x. f x = g x)      
let th = list_gen_rule [f;g] th11                      //                  |- !(f:'a->'b) g. f = g <=> (!x. f x = g x)

(***hide***)
//let th1 = @"\x. (f:'a->'b) x" |> parse_term |> eta_conv_tr
//let th2 = sym_rule_tr th1
//let th3 = @"!x. (f:'a->'b) x = g x" |> parse_term |> assume_rule_tr
//let th4 = spec_rule_tr x th3
//let th5 = mk_abs_rule_tr x th4
//let th6 = @"\x. (g:'a->'b) x" |> parse_term |> eta_conv_tr
//let th7 = [th2; th5; th6] |> list_trans_rule_tr
//let th8 = @"(f:'a->'b)=g" |> parse_term |> assume_rule_tr
//let th9 = mk_comb1_rule_tr th8 x
//let th10 = gen_rule_tr x th9
//let th11 = deduct_antisym_rule_tr th7 th10
//let th = list_gen_rule_tr [f;g] th11
(***unhide***)

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

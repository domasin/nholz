(**
distribuzione della negazione sulla disgiunzione
=============

$\forall p\ q.\ \neg (p \vee q) \Leftrightarrow \neg p \wedge \neg q$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

not_dist_disj_thm
//   |- !p q. ~ (p \/ q) <=> ~ p /\ ~ q

(**
Backward proof with tree
*)

([],"!p q. ~ (p \/ q) <=> ~ p /\ ~ q")
|> start_proof
|> list_gen_rule_bk
    |> deduct_antisym_rule_bk [] []
        (* ~ p /\ ~ q |- ~ (p \/ q)        *)
        |> not_intro_rule_bk
            |> disch_rule_bk
                (* ~ p /\ ~ q, p \/ q |- false   *)
                |> disj_cases_rule_bk [1] [0] [0] "p:bool" "q:bool"
                    |> assume_rule_bk
                    (* ~ p /\ ~ q, p |- false        *)
                    |> undisch_rule_bk 1
                        |> not_elim_rule_bk
                            |> conjunct1_rule_bk "~ q"
                                |> assume_rule_bk
                    (* ~ p /\ ~ q, q |- false        *)
                    |> undisch_rule_bk 1
                        |> not_elim_rule_bk
                            |> conjunct2_rule_bk "~ p"
                                |> assume_rule_bk
        (* ~ (p \/ q) |- ~ p /\ ~ q        *)
        |> conj_rule_bk [0] [0]
            (* ~ (p \/ q) |- ~ p               *)
            |> deduct_contrapos_rule_bk 0
                (* p |- p \/ q                      *)
                |> disj1_rule_bk
                    |> assume_rule_bk
            (* ~ (p \/ q) |- ~ q               *)
            |> deduct_contrapos_rule_bk 0
                (* q |- p \/ q                      *)
                |> disj2_rule_bk
                    |> assume_rule_bk

|> view

//val it : thm = |- !p q. ~ (p \/ q) <=> ~ p /\ ~ q

(**
$
\small{ 	\color{green}{\dfrac
	{[p:bool;q:bool]
	\qquad
	\color{green}{\dfrac
		{\color{green}{\dfrac
			{\color{green}{\dfrac
				{p\ \vee\ q
				\qquad
				\color{green}{\dfrac
					{\color{green}{\dfrac
						{p\ \vee\ q}
						{p\ \vee\ q\ \vdash\ p\ \vee\ q}
						\textsf{ assume_rule}}
					\qquad
					\color{green}{\dfrac
						{\color{green}{\dfrac
							{\color{green}{\dfrac
								{\color{green}{\dfrac
									{\neg\ p\ \wedge\ \neg\ q}
									{\neg\ p\ \wedge\ \neg\ q\ \vdash\ \neg\ p\ \wedge\ \neg\ q}
									\textsf{ assume_rule}}}
								{\neg\ p\ \wedge\ \neg\ q\ \vdash\ \neg\ p}
								\textsf{ conjunct1_rule}}}
							{\neg\ p\ \wedge\ \neg\ q\ \vdash\ p\ \Rightarrow\ \bot}
							\textsf{ not_elim_rule}}}
						{\neg\ p\ \wedge\ \neg\ q,\ p\ \vdash\ \bot}
						\textsf{ undisch_rule}}
					\qquad
					\color{green}{\dfrac
						{\color{green}{\dfrac
							{\color{green}{\dfrac
								{\color{green}{\dfrac
									{\neg\ p\ \wedge\ \neg\ q}
									{\neg\ p\ \wedge\ \neg\ q\ \vdash\ \neg\ p\ \wedge\ \neg\ q}
									\textsf{ assume_rule}}}
								{\neg\ p\ \wedge\ \neg\ q\ \vdash\ \neg\ q}
								\textsf{ conjunct2_rule}}}
							{\neg\ p\ \wedge\ \neg\ q\ \vdash\ q\ \Rightarrow\ \bot}
							\textsf{ not_elim_rule}}}
						{\neg\ p\ \wedge\ \neg\ q,\ q\ \vdash\ \bot}
						\textsf{ undisch_rule}}}
					{p\ \vee\ q,\ \neg\ p\ \wedge\ \neg\ q\ \vdash\ \bot}
					\textsf{ disj_cases_rule}}}
				{\neg\ p\ \wedge\ \neg\ q\ \vdash\ p\ \vee\ q\ \Rightarrow\ \bot}
				\textsf{ disch_rule}}}
			{\neg\ p\ \wedge\ \neg\ q\ \vdash\ \neg\ (p\ \vee\ q)}
			\textsf{ not_intro_rule}}
		\qquad
		\color{green}{\dfrac
			{\color{green}{\dfrac
				{p:bool
				\qquad
				\color{green}{\dfrac
					{\color{green}{\dfrac
						{p:bool}
						{p\ \vdash\ p}
						\textsf{ assume_rule}}
					\qquad
					q:bool}
					{p\ \vdash\ p\ \vee\ q}
					\textsf{ disj1_rule}}}
				{\neg\ (p\ \vee\ q)\ \vdash\ \neg\ p}
				\textsf{ deduct_contrapos_rule}}
			\qquad
			\color{green}{\dfrac
				{q:bool
				\qquad
				\color{green}{\dfrac
					{p:bool
					\qquad
					\color{green}{\dfrac
						{q:bool}
						{q\ \vdash\ q}
						\textsf{ assume_rule}}}
					{q\ \vdash\ p\ \vee\ q}
					\textsf{ disj2_rule}}}
				{\neg\ (p\ \vee\ q)\ \vdash\ \neg\ q}
				\textsf{ deduct_contrapos_rule}}}
			{\neg\ (p\ \vee\ q)\ \vdash\ \neg\ p\ \wedge\ \neg\ q}
			\textsf{ conj_rule}}}
		{\vdash\ \neg\ (p\ \vee\ q)\ \Leftrightarrow\ \neg\ p\ \wedge\ \neg\ q}
		\textsf{ deduct_antisym_rule}}}
	{\vdash\ \forall\ p\ q.\ \neg\ (p\ \vee\ q)\ \Leftrightarrow\ \neg\ p\ \wedge\ \neg\ q}
	\textsf{ list_gen_rule}} }
$
*)

it
|> root
|> linearizeProof

// 0                             p \/ q |- p \/ q                                             assume_rule                         
// 1                         ~ p /\ ~ q |- ~ p /\ ~ q                                         assume_rule                         
// 2                         ~ p /\ ~ q |- ~ p                                                conjunct1_rule            1         
// 3                         ~ p /\ ~ q |- p ==> false                                        not_elim_rule             2         
// 4                 ~ p /\ ~ q, p:bool |- false                                              undisch_rule              3         
// 5                         ~ p /\ ~ q |- ~ p /\ ~ q                                         assume_rule                         
// 6                         ~ p /\ ~ q |- ~ q                                                conjunct2_rule            5         
// 7                         ~ p /\ ~ q |- q ==> false                                        not_elim_rule             6         
// 8                 ~ p /\ ~ q, q:bool |- false                                              undisch_rule              7         
// 9                 p \/ q, ~ p /\ ~ q |- false                                              disj_cases_rule           0,4,8     
// 10                        ~ p /\ ~ q |- p \/ q ==> false                                   disch_rule                9         
// 11                        ~ p /\ ~ q |- ~ (p \/ q)                                         not_intro_rule            10        
// 12                            p:bool |- p:bool                                             assume_rule                         
// 13                            p:bool |- p \/ q                                             disj1_rule                12        
// 14                        ~ (p \/ q) |- ~ p                                                deduct_contrapos_rule     13        
// 15                            q:bool |- q:bool                                             assume_rule                         
// 16                            q:bool |- p \/ q                                             disj2_rule                15        
// 17                        ~ (p \/ q) |- ~ q                                                deduct_contrapos_rule     16        
// 18                        ~ (p \/ q) |- ~ p /\ ~ q                                         conj_rule                 14,17     
// 19                                   |- ~ (p \/ q) <=> ~ p /\ ~ q                          deduct_antisym_rule       11,18     
// 20                                   |- !p q. ~ (p \/ q) <=> ~ p /\ ~ q                    list_gen_rule             19        

(**
Forward proof with tree
*)

let p = parse_term(@"p:bool")
let q = parse_term(@"q:bool")

list_gen_rule_fd [p;q]
  (deduct_antisym_rule_fd
    (* ~ p /\ ~ q |- ~ (p \/ q)        *)
    (not_intro_rule_fd
      (disch_rule_fd (parse_term(@"p \/ q"))
        (* ~ p /\ ~ q, p \/ q |- false   *)
        (disj_cases_rule_fd (assume_rule_fd (parse_term(@"p \/ q")))
          (* ~ p /\ ~ q, p |- false        *)
          (undisch_rule_fd (not_elim_rule_fd (conjunct1_rule_fd (assume_rule_fd (parse_term(@"~ p /\ ~ q"))))))
          (* ~ p /\ ~ q, q |- false        *)
          (undisch_rule_fd (not_elim_rule_fd (conjunct2_rule_fd (assume_rule_fd (parse_term(@"~ p /\ ~ q")))))) )))
    (* ~ (p \/ q) |- ~ p /\ ~ q        *)
    (conj_rule_fd
      (* ~ (p \/ q) |- ~ p               *)
      (deduct_contrapos_rule_fd p
        (* p |- p \/ q                      *)
        (disj1_rule_fd (assume_rule_fd p) q) )
      (* ~ (p \/ q) |- ~ q               *)
      (deduct_contrapos_rule_fd q
        (* q |- p \/ q                      *)
        (disj2_rule_fd p (assume_rule_fd q)) )))
|> zipper
//|> view //equals backward version
|> loc_thm |> Option.get

//val it : thm = |- !p q. ~ (p \/ q) <=> ~ p /\ ~ q

(**
Classic forward proof without tree
*)

let th1 = assume_rule (parse_term(@"~ p /\ ~ q")) in
list_gen_rule [p;q]
    (deduct_antisym_rule
      (* ~ p /\ ~ q |- ~ (p \/ q)        *)
      (not_intro_rule
        (disch_rule (parse_term(@"p \/ q"))
          (* ~ p /\ ~ q, p \/ q |- false   *)
          (disj_cases_rule (assume_rule (parse_term(@"p \/ q")))
            (* ~ p /\ ~ q, p |- false        *)
            (undisch_rule (not_elim_rule (conjunct1_rule th1)))
            (* ~ p /\ ~ q, q |- false        *)
            (undisch_rule (not_elim_rule (conjunct2_rule th1))) )))
      (* ~ (p \/ q) |- ~ p /\ ~ q        *)
      (conj_rule
        (* ~ (p \/ q) |- ~ p               *)
        (deduct_contrapos_rule p
          (* p |- p \/ q                      *)
          (disj1_rule (assume_rule p) q) )
        (* ~ (p \/ q) |- ~ q               *)
        (deduct_contrapos_rule q
          (* q |- p \/ q                      *)
          (disj2_rule p (assume_rule q)) )))

//val it : thm = |- !p q. ~ (p \/ q) <=> ~ p /\ ~ q
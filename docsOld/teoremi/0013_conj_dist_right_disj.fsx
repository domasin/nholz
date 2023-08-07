(**
distributivit&agrave; a destra della congiunzione sulla disgiunzione
=============

$\forall p\ q\ r.\ p \wedge (q \vee r) \Leftrightarrow (p \wedge q) \vee (p \wedge r)$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_dist_right_disj_thm
//   |- !p q r. p /\ (q \/ r) <=> (p /\ q) \/ (p /\ r)

(**
Backward proof with tree
*)

([],"!p q r. p /\ (q \/ r) <=> (p /\ q) \/ (p /\ r)")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> conj_rule_bk [0] [0]
|> disj_cases_rule_bk [0] [] [] "(p /\ q)" "(p /\ r)"
|> assume_rule_bk
|> conjunct1_rule_bk "q:bool"
|> assume_rule_bk
|> conjunct1_rule_bk "r:bool"
|> assume_rule_bk
|> disj_cases_rule_bk [0] [] [] "(p /\ q)" "(p /\ r)"
|> assume_rule_bk
|> disj1_rule_bk
|> conjunct2_rule_bk "p:bool"
|> assume_rule_bk
|> disj2_rule_bk
|> conjunct2_rule_bk "p:bool"
|> assume_rule_bk
|> disj_cases_rule_bk [0] [0] [0] "q:bool" "r:bool"
|> conjunct2_rule_bk "p:bool"
|> assume_rule_bk
|> disj1_rule_bk
|> conj_rule_bk [0] [1]
|> conjunct1_rule_bk "q \/ r"
|> assume_rule_bk
|> assume_rule_bk
|> disj2_rule_bk
|> conj_rule_bk [0] [1]
|> conjunct1_rule_bk "q \/ r"
|> assume_rule_bk
|> assume_rule_bk
|> view

(**
$
\small{ 	\color{green}{\dfrac
	{[p:bool;q:bool;r:bool]
	\qquad
	\color{green}{\dfrac
		{\color{green}{\dfrac
			{\color{green}{\dfrac
				{\color{green}{\dfrac
					{p\ \wedge\ q\ \vee\ p\ \wedge\ r}
					{p\ \wedge\ q\ \vee\ p\ \wedge\ r\ \vdash\ p\ \wedge\ q\ \vee\ p\ \wedge\ r}
					\textsf{ assume_rule}}
				\qquad
				\color{green}{\dfrac
					{\color{green}{\dfrac
						{p\ \wedge\ q}
						{p\ \wedge\ q\ \vdash\ p\ \wedge\ q}
						\textsf{ assume_rule}}}
					{p\ \wedge\ q\ \vdash\ p}
					\textsf{ conjunct1_rule}}
				\qquad
				\color{green}{\dfrac
					{\color{green}{\dfrac
						{p\ \wedge\ r}
						{p\ \wedge\ r\ \vdash\ p\ \wedge\ r}
						\textsf{ assume_rule}}}
					{p\ \wedge\ r\ \vdash\ p}
					\textsf{ conjunct1_rule}}}
				{p\ \wedge\ q\ \vee\ p\ \wedge\ r\ \vdash\ p}
				\textsf{ disj_cases_rule}}
			\qquad
			\color{green}{\dfrac
				{\color{green}{\dfrac
					{p\ \wedge\ q\ \vee\ p\ \wedge\ r}
					{p\ \wedge\ q\ \vee\ p\ \wedge\ r\ \vdash\ p\ \wedge\ q\ \vee\ p\ \wedge\ r}
					\textsf{ assume_rule}}
				\qquad
				\color{green}{\dfrac
					{\color{green}{\dfrac
						{\color{green}{\dfrac
							{p\ \wedge\ q}
							{p\ \wedge\ q\ \vdash\ p\ \wedge\ q}
							\textsf{ assume_rule}}}
						{p\ \wedge\ q\ \vdash\ q}
						\textsf{ conjunct2_rule}}
					\qquad
					r:bool}
					{p\ \wedge\ q\ \vdash\ q\ \vee\ r}
					\textsf{ disj1_rule}}
				\qquad
				\color{green}{\dfrac
					{q:bool
					\qquad
					\color{green}{\dfrac
						{\color{green}{\dfrac
							{p\ \wedge\ r}
							{p\ \wedge\ r\ \vdash\ p\ \wedge\ r}
							\textsf{ assume_rule}}}
						{p\ \wedge\ r\ \vdash\ r}
						\textsf{ conjunct2_rule}}}
					{p\ \wedge\ r\ \vdash\ q\ \vee\ r}
					\textsf{ disj2_rule}}}
				{p\ \wedge\ q\ \vee\ p\ \wedge\ r\ \vdash\ q\ \vee\ r}
				\textsf{ disj_cases_rule}}}
			{p\ \wedge\ q\ \vee\ p\ \wedge\ r\ \vdash\ p\ \wedge\ (q\ \vee\ r)}
			\textsf{ conj_rule}}
		\qquad
		\color{green}{\dfrac
			{\color{green}{\dfrac
				{\color{green}{\dfrac
					{p\ \wedge\ (q\ \vee\ r)}
					{p\ \wedge\ (q\ \vee\ r)\ \vdash\ p\ \wedge\ (q\ \vee\ r)}
					\textsf{ assume_rule}}}
				{p\ \wedge\ (q\ \vee\ r)\ \vdash\ q\ \vee\ r}
				\textsf{ conjunct2_rule}}
			\qquad
			\color{green}{\dfrac
				{\color{green}{\dfrac
					{\color{green}{\dfrac
						{\color{green}{\dfrac
							{p\ \wedge\ (q\ \vee\ r)}
							{p\ \wedge\ (q\ \vee\ r)\ \vdash\ p\ \wedge\ (q\ \vee\ r)}
							\textsf{ assume_rule}}}
						{p\ \wedge\ (q\ \vee\ r)\ \vdash\ p}
						\textsf{ conjunct1_rule}}
					\qquad
					\color{green}{\dfrac
						{q:bool}
						{q\ \vdash\ q}
						\textsf{ assume_rule}}}
					{p\ \wedge\ (q\ \vee\ r),\ q\ \vdash\ p\ \wedge\ q}
					\textsf{ conj_rule}}
				\qquad
				p\ \wedge\ r}
				{p\ \wedge\ (q\ \vee\ r),\ q\ \vdash\ p\ \wedge\ q\ \vee\ p\ \wedge\ r}
				\textsf{ disj1_rule}}
			\qquad
			\color{green}{\dfrac
				{p\ \wedge\ q
				\qquad
				\color{green}{\dfrac
					{\color{green}{\dfrac
						{\color{green}{\dfrac
							{p\ \wedge\ (q\ \vee\ r)}
							{p\ \wedge\ (q\ \vee\ r)\ \vdash\ p\ \wedge\ (q\ \vee\ r)}
							\textsf{ assume_rule}}}
						{p\ \wedge\ (q\ \vee\ r)\ \vdash\ p}
						\textsf{ conjunct1_rule}}
					\qquad
					\color{green}{\dfrac
						{r:bool}
						{r\ \vdash\ r}
						\textsf{ assume_rule}}}
					{p\ \wedge\ (q\ \vee\ r),\ r\ \vdash\ p\ \wedge\ r}
					\textsf{ conj_rule}}}
				{p\ \wedge\ (q\ \vee\ r),\ r\ \vdash\ p\ \wedge\ q\ \vee\ p\ \wedge\ r}
				\textsf{ disj2_rule}}}
			{p\ \wedge\ (q\ \vee\ r)\ \vdash\ p\ \wedge\ q\ \vee\ p\ \wedge\ r}
			\textsf{ disj_cases_rule}}}
		{\vdash\ p\ \wedge\ (q\ \vee\ r)\ \Leftrightarrow\ p\ \wedge\ q\ \vee\ p\ \wedge\ r}
		\textsf{ deduct_antisym_rule}}}
	{\vdash\ \forall\ p\ q\ r.\ p\ \wedge\ (q\ \vee\ r)\ \Leftrightarrow\ p\ \wedge\ q\ \vee\ p\ \wedge\ r}
	\textsf{ list_gen_rule}} }
$
*)

it
|> root
|> linearizeProof

// 0                   p /\ q \/ p /\ r |- p /\ q \/ p /\ r                                   assume_rule                         
// 1                             p /\ q |- p /\ q                                             assume_rule                         
// 2                             p /\ q |- p:bool                                             conjunct1_rule            1         
// 3                             p /\ r |- p /\ r                                             assume_rule                         
// 4                             p /\ r |- p:bool                                             conjunct1_rule            3         
// 5                   p /\ q \/ p /\ r |- p:bool                                             disj_cases_rule           0,2,4     
// 6                   p /\ q \/ p /\ r |- p /\ q \/ p /\ r                                   assume_rule                         
// 7                             p /\ q |- p /\ q                                             assume_rule                         
// 8                             p /\ q |- q:bool                                             conjunct2_rule            7         
// 9                             p /\ q |- q \/ r                                             disj1_rule                8         
// 10                            p /\ r |- p /\ r                                             assume_rule                         
// 11                            p /\ r |- r:bool                                             conjunct2_rule            10        
// 12                            p /\ r |- q \/ r                                             disj2_rule                11        
// 13                  p /\ q \/ p /\ r |- q \/ r                                             disj_cases_rule           6,9,12    
// 14                  p /\ q \/ p /\ r |- p /\ (q \/ r)                                      conj_rule                 5,13      
// 15                     p /\ (q \/ r) |- p /\ (q \/ r)                                      assume_rule                         
// 16                     p /\ (q \/ r) |- q \/ r                                             conjunct2_rule            15        
// 17                     p /\ (q \/ r) |- p /\ (q \/ r)                                      assume_rule                         
// 18                     p /\ (q \/ r) |- p:bool                                             conjunct1_rule            17        
// 19                            q:bool |- q:bool                                             assume_rule                         
// 20             p /\ (q \/ r), q:bool |- p /\ q                                             conj_rule                 18,19     
// 21             p /\ (q \/ r), q:bool |- p /\ q \/ p /\ r                                   disj1_rule                20        
// 22                     p /\ (q \/ r) |- p /\ (q \/ r)                                      assume_rule                         
// 23                     p /\ (q \/ r) |- p:bool                                             conjunct1_rule            22        
// 24                            r:bool |- r:bool                                             assume_rule                         
// 25             p /\ (q \/ r), r:bool |- p /\ r                                             conj_rule                 23,24     
// 26             p /\ (q \/ r), r:bool |- p /\ q \/ p /\ r                                   disj2_rule                25        
// 27                     p /\ (q \/ r) |- p /\ q \/ p /\ r                                   disj_cases_rule           16,21,26  
// 28                                   |- p /\ (q \/ r) <=> p /\ q \/ p /\ r                 deduct_antisym_rule       14,27     
// 29                                   |- !p q r. p /\ (q \/ r) <=> p /\ q \/ p /\ r         list_gen_rule             28        

(**
Forward proof with tree
*)

let th1 = assume_rule_fd (parse_term(@"(p /\ q) \/ (p /\ r)"))
let th2 = assume_rule_fd (parse_term(@"p /\ (q \/ r)")) 
list_gen_rule [p;q;r]
(deduct_antisym_rule_fd
  (* (p /\ q) \/ (p /\ r) |- p /\ (q \/ r)  *)
  (conj_rule_fd
    (* (p /\ q) \/ (p /\ r) |- p              *)
    (disj_cases_rule_fd th1
      (conjunct1_rule_fd (assume_rule_fd (parse_term(@"p /\ q"))))
      (conjunct1_rule_fd (assume_rule_fd (parse_term(@"p /\ r")))) )
    (* (p /\ q) \/ (p /\ r) |- q \/ r         *)
    (disj_cases_rule_fd th1
      (disj1_rule_fd (conjunct2_rule_fd (assume_rule_fd (parse_term(@"p /\ q")))) r)
      (disj2_rule_fd q (conjunct2_rule_fd (assume_rule_fd (parse_term(@"p /\ r"))))) ))
  (* p /\ (q \/ r) |- (p /\ q) \/ (p /\ r)  *)
  (disj_cases_rule_fd (conjunct2_rule_fd th2)
    (disj1_rule_fd
      (* p /\ (q \/ r), q |- p /\ q             *)
      (conj_rule_fd (conjunct1_rule_fd th2) (assume_rule_fd q)) (parse_term(@"p /\ r")))
    (disj2_rule_fd (parse_term(@"p /\ q"))
      (* p /\ (q \/ r), r |- p /\ r             *)
      (conj_rule_fd (conjunct1_rule_fd th2) (assume_rule_fd r)) )))
|> linearizeProof

// 0                   p /\ q \/ p /\ r |- p /\ q \/ p /\ r                                   assume_rule                         
// 1                             p /\ q |- p /\ q                                             assume_rule                         
// 2                             p /\ q |- p:bool                                             conjunct1_rule            1         
// 3                             p /\ r |- p /\ r                                             assume_rule                         
// 4                             p /\ r |- p:bool                                             conjunct1_rule            3         
// 5                   p /\ q \/ p /\ r |- p:bool                                             disj_cases_rule           0,2,4     
// 6                   p /\ q \/ p /\ r |- p /\ q \/ p /\ r                                   assume_rule                         
// 7                             p /\ q |- p /\ q                                             assume_rule                         
// 8                             p /\ q |- q:bool                                             conjunct2_rule            7         
// 9                             p /\ q |- q \/ r                                             disj1_rule                8         
// 10                            p /\ r |- p /\ r                                             assume_rule                         
// 11                            p /\ r |- r:bool                                             conjunct2_rule            10        
// 12                            p /\ r |- q \/ r                                             disj2_rule                11        
// 13                  p /\ q \/ p /\ r |- q \/ r                                             disj_cases_rule           6,9,12    
// 14                  p /\ q \/ p /\ r |- p /\ (q \/ r)                                      conj_rule                 5,13      
// 15                     p /\ (q \/ r) |- p /\ (q \/ r)                                      assume_rule                         
// 16                     p /\ (q \/ r) |- q \/ r                                             conjunct2_rule            15        
// 17                     p /\ (q \/ r) |- p /\ (q \/ r)                                      assume_rule                         
// 18                     p /\ (q \/ r) |- p:bool                                             conjunct1_rule            17        
// 19                            q:bool |- q:bool                                             assume_rule                         
// 20             p /\ (q \/ r), q:bool |- p /\ q                                             conj_rule                 18,19     
// 21             p /\ (q \/ r), q:bool |- p /\ q \/ p /\ r                                   disj1_rule                20        
// 22                     p /\ (q \/ r) |- p /\ (q \/ r)                                      assume_rule                         
// 23                     p /\ (q \/ r) |- p:bool                                             conjunct1_rule            22        
// 24                            r:bool |- r:bool                                             assume_rule                         
// 25             p /\ (q \/ r), r:bool |- p /\ r                                             conj_rule                 23,24     
// 26             p /\ (q \/ r), r:bool |- p /\ q \/ p /\ r                                   disj2_rule                25        
// 27                     p /\ (q \/ r) |- p /\ q \/ p /\ r                                   disj_cases_rule           16,21,26  
// 28                                   |- p /\ (q \/ r) <=> p /\ q \/ p /\ r                 deduct_antisym_rule       14,27     

(**
Classic forward proof without tree
*)

let th1' = assume_rule (parse_term(@"(p /\ q) \/ (p /\ r)")) in
let th2' = assume_rule (parse_term(@"p /\ (q \/ r)")) in
list_gen_rule [p;q;r]
  (deduct_antisym_rule
    (* (p /\ q) \/ (p /\ r) |- p /\ (q \/ r)  *)
    (conj_rule
      (* (p /\ q) \/ (p /\ r) |- p              *)
      (disj_cases_rule th1'
        (conjunct1_rule (assume_rule (parse_term(@"p /\ q"))))
        (conjunct1_rule (assume_rule (parse_term(@"p /\ r")))) )
      (* (p /\ q) \/ (p /\ r) |- q \/ r         *)
      (disj_cases_rule th1'
        (disj1_rule (conjunct2_rule (assume_rule (parse_term(@"p /\ q")))) r)
        (disj2_rule q (conjunct2_rule (assume_rule (parse_term(@"p /\ r"))))) ))
    (* p /\ (q \/ r) |- (p /\ q) \/ (p /\ r)  *)
    (disj_cases_rule (conjunct2_rule th2')
      (disj1_rule
        (* p /\ (q \/ r), q |- p /\ q             *)
        (conj_rule (conjunct1_rule th2') (assume_rule q)) (parse_term(@"p /\ r")))
      (disj2_rule (parse_term(@"p /\ q"))
        (* p /\ (q \/ r), r |- p /\ r             *)
        (conj_rule (conjunct1_rule th2') (assume_rule r)) )))
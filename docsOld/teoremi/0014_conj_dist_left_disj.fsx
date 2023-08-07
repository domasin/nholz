(**
distributivit&agrave; a sinistra della congiunzione sulla disgiunzione
=============

$\forall p\ q\ r.\ (p \vee q) \wedge r \Leftrightarrow (p \wedge r) \vee (q \wedge r)$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
BoolAlg.load
(***unhide***)

conj_dist_left_disj_thm
//   |- !p q r. (p \/ q) /\ r <=> (p /\ r) \/ (q /\ r)

(**
Backward proof with tree
*)

([],"!p q r. (p \/ q) /\ r <=> (p /\ r) \/ (q /\ r)")
|> start_proof
|> list_gen_rule_bk
|> trans_rule_bk "(r /\ p) \/ (r /\ q)"
|> trans_rule_bk "r /\ (p \/ q)"
|> list_spec_rule_bk [("p \/ q","p:bool"); ("r:bool","q:bool")]
|> by conj_comm_thm "conj_comm_thm"
|> list_spec_rule_bk [("r:bool","p:bool"); ("p:bool","q:bool"); ("q:bool","r:bool")]
|> by conj_dist_right_disj_thm "conj_dist_right_disj_thm"
|> mk_bin_rule_bk [] []
|> list_spec_rule_bk [("r:bool","p:bool"); ("p:bool","q:bool")]
|> by conj_comm_thm "conj_comm_thm"
|> list_spec_rule_bk [("r:bool","p:bool"); ("q:bool","q:bool")]
|> by conj_comm_thm "conj_comm_thm"
|> view

(**
$
\small{ 	\color{green}{\dfrac
	{[p:bool;q:bool;r:bool]
	\qquad
	\color{green}{\dfrac
		{\color{green}{\dfrac
			{\color{green}{\dfrac
				{[p\ \vee\ q;r:bool]
				\qquad
				\dfrac
					{}
					{\vdash\ \forall\ p\ q.\ p\ \wedge\ q\ \Leftrightarrow\ q\ \wedge\ p}
					\textsf{ conj_comm_thm}}
				{\vdash\ (p\ \vee\ q)\ \wedge\ r\ \Leftrightarrow\ r\ \wedge\ (p\ \vee\ q)}
				\textsf{ list_spec_rule}}
			\qquad
			\color{green}{\dfrac
				{[r:bool;p:bool;q:bool]
				\qquad
				\dfrac
					{}
					{\vdash\ \forall\ p\ q\ r.\ p\ \wedge\ (q\ \vee\ r)\ \Leftrightarrow\ p\ \wedge\ q\ \vee\ p\ \wedge\ r}
					\textsf{ conj_dist_right_disj_thm}}
				{\vdash\ r\ \wedge\ (p\ \vee\ q)\ \Leftrightarrow\ r\ \wedge\ p\ \vee\ r\ \wedge\ q}
				\textsf{ list_spec_rule}}}
			{\vdash\ (p\ \vee\ q)\ \wedge\ r\ \Leftrightarrow\ r\ \wedge\ p\ \vee\ r\ \wedge\ q}
			\textsf{ trans_rule}}
		\qquad
		\color{green}{\dfrac
			{\$\vee
			\qquad
			\color{green}{\dfrac
				{[r:bool;p:bool]
				\qquad
				\dfrac
					{}
					{\vdash\ \forall\ p\ q.\ p\ \wedge\ q\ \Leftrightarrow\ q\ \wedge\ p}
					\textsf{ conj_comm_thm}}
				{\vdash\ r\ \wedge\ p\ \Leftrightarrow\ p\ \wedge\ r}
				\textsf{ list_spec_rule}}
			\qquad
			\color{green}{\dfrac
				{[r:bool;q:bool]
				\qquad
				\dfrac
					{}
					{\vdash\ \forall\ p\ q.\ p\ \wedge\ q\ \Leftrightarrow\ q\ \wedge\ p}
					\textsf{ conj_comm_thm}}
				{\vdash\ r\ \wedge\ q\ \Leftrightarrow\ q\ \wedge\ r}
				\textsf{ list_spec_rule}}}
			{\vdash\ r\ \wedge\ p\ \vee\ r\ \wedge\ q\ \Leftrightarrow\ p\ \wedge\ r\ \vee\ q\ \wedge\ r}
			\textsf{ mk_bin_rule}}}
		{\vdash\ (p\ \vee\ q)\ \wedge\ r\ \Leftrightarrow\ p\ \wedge\ r\ \vee\ q\ \wedge\ r}
		\textsf{ trans_rule}}}
	{\vdash\ \forall\ p\ q\ r.\ (p\ \vee\ q)\ \wedge\ r\ \Leftrightarrow\ p\ \wedge\ r\ \vee\ q\ \wedge\ r}
	\textsf{ list_gen_rule}} }
$
*)

it
|> root
|> linearizeProof

// 0    |- !p q. p /\ q <=> q /\ p                            conj_comm_thm                       
// 1    |- (p \/ q) /\ r <=> r /\ (p \/ q)                    list_spec_rule            0         
// 2    |- !p q r. p /\ (q \/ r) <=> p /\ q \/ p /\ r         conj_dist_right_disj_thm            
// 3    |- r /\ (p \/ q) <=> r /\ p \/ r /\ q                 list_spec_rule            2         
// 4    |- (p \/ q) /\ r <=> r /\ p \/ r /\ q                 trans_rule                1,3       
// 5    |- !p q. p /\ q <=> q /\ p                            conj_comm_thm                       
// 6    |- r /\ p <=> p /\ r                                  list_spec_rule            5         
// 7    |- !p q. p /\ q <=> q /\ p                            conj_comm_thm                       
// 8    |- r /\ q <=> q /\ r                                  list_spec_rule            7         
// 9    |- r /\ p \/ r /\ q <=> p /\ r \/ q /\ r              mk_bin_rule               6,8       
// 10   |- (p \/ q) /\ r <=> p /\ r \/ q /\ r                 trans_rule                4,9       
// 11   |- !p q r. (p \/ q) /\ r <=> p /\ r \/ q /\ r         list_gen_rule             10        

(**
Forward proof with tree
*)

list_gen_rule_fd [p;q;r]
    (list_trans_rule_fd
       [ list_spec_rule_fd [(parse_term(@"p\/q"));r] (conj_comm_thm |> thm_fd "conj_comm_thm");
         list_spec_rule_fd [r;p;q] (conj_dist_right_disj_thm |> thm_fd "conj_dist_right_disj_thm");
         mk_bin_rule_fd (parse_term(@"$\/"))
           (list_spec_rule_fd [r;p] (conj_comm_thm |> thm_fd "conj_comm_thm"))
           (list_spec_rule_fd [r;q] (conj_comm_thm |> thm_fd "conj_comm_thm")) ])
|> zipper
|> view

(**
Classic forward proof without tree
*)

list_gen_rule [p;q;r]
  (list_trans_rule
     [ list_spec_rule [(parse_term(@"p\/q"));r] conj_comm_thm;
       list_spec_rule [r;p;q] conj_dist_right_disj_thm;
       mk_bin_rule (parse_term(@"$\/"))
         (list_spec_rule [r;p] conj_comm_thm)
         (list_spec_rule [r;q] conj_comm_thm) ])

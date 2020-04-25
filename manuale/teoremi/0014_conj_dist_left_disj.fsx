(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_dist_left_disj_thm
//   |- !p q r. (p \/ q) /\ r <=> (p /\ r) \/ (q /\ r)

list_gen_rule_fd [p;q;r]
    (list_trans_rule_fd
       [ list_spec_rule_fd [(parse_term(@"p\/q"));r] (conj_comm_thm |> thm_fd "conj\_comm\_thm");
         list_spec_rule_fd [r;p;q] (conj_dist_right_disj_thm |> thm_fd "conj\_dist\_right\_disj_\thm");
         mk_bin_rule_fd (parse_term(@"$\/"))
           (list_spec_rule_fd [r;p] (conj_comm_thm |> thm_fd "conj\_comm\_thm"))
           (list_spec_rule_fd [r;q] (conj_comm_thm |> thm_fd "conj\_comm\_thm")) ])
|> zipper
|> view
//|> linearizeProof

//([],"!p q r. (p \/ q) /\ r <=> (p /\ r) \/ (q /\ r)")
//|> start_proof
//|> list_gen_rule_bk
//|> deduct_antisym_rule_bk [] []
//|> conj_rule_bk [0] [0]
//|> disj_cases_rule_bk [0] [] [] "p /\ r" "q /\ r"
//|> assume_rule_bk
//|> disj1_rule_bk
//|> conjunct1_rule_bk "r:bool"
//|> assume_rule_bk
//|> disj2_rule_bk
//|> conjunct1_rule_bk "r:bool"
//|> assume_rule_bk
//|> disj_cases_rule_bk [0] [] [] "p /\ r" "q /\ r"
//|> assume_rule_bk
//|> conjunct2_rule_bk "p:bool"
//|> assume_rule_bk
//|> conjunct2_rule_bk "q:bool"
//|> assume_rule_bk

//|> disj_cases_rule_bk [0] [0] [0] "p:bool" "q:bool"
//|> conjunct1_rule_bk "r:bool"
//|> assume_rule_bk

//|> disj1_rule_bk
//|> conj_rule_bk [1] [0]
//|> assume_rule_bk
//|> conjunct2_rule_bk "p \/ q"
//|> assume_rule_bk
//|> disj2_rule_bk
//|> conj_rule_bk [1] [0]
//|> assume_rule_bk
//|> conjunct2_rule_bk "p \/ q"
//|> assume_rule_bk

////|> view
//|> root
//|> linearizeProof


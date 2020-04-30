(**
commutabilit&agrave; della disgiunzione
=============

$\forall p\ q.\ p \vee q \Leftrightarrow q \vee p$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

disj_comm_thm
//   |- !p q. p \/ q <=> q \/ p

(**
Backward proof with tree
*)

([],"!p q. p \/ q <=> q \/ p")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> disj_cases_rule_bk [0] [] [] "q:bool" "p:bool"
|> assume_rule_bk
|> disj2_rule_bk
|> assume_rule_bk
|> disj1_rule_bk
|> assume_rule_bk
|> disj_cases_rule_bk [0] [] [] "p:bool" "q:bool"
|> assume_rule_bk
|> disj2_rule_bk
|> assume_rule_bk
|> disj1_rule_bk
|> assume_rule_bk

|> view

let th = 
    disj_cases_rule_fd                     (* p \/ q |- q \/ p      *)
        (assume_rule_fd (parse_term(@"p \/ q")))
        (disj2_rule_fd q (assume_rule_fd p))
        (disj1_rule_fd (assume_rule_fd q) p)
    |> zipper
    |> view
    |> loc_thm 
    |> Option.get

([],"!p q. p \/ q <=> q \/ p")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> inst_rule_bk [(p,q);(q,p)]
|> disj_cases_rule_bk [0] [] [] "p:bool" "q:bool"
|> assume_rule_bk
|> disj2_rule_bk
|> assume_rule_bk
|> disj1_rule_bk
|> assume_rule_bk
|> disj_cases_rule_bk [0] [] [] "p:bool" "q:bool"
|> assume_rule_bk
|> disj2_rule_bk
|> assume_rule_bk
|> disj1_rule_bk
|> assume_rule_bk
|> view

let th1 = disj_cases_rule_fd                     (* p \/ q |- q \/ p      *)
            (assume_rule_fd (parse_term(@"p \/ q")))
            (disj2_rule_fd q (assume_rule_fd p))
            (disj1_rule_fd (assume_rule_fd q) p) in
let th2 = inst_rule_fd [(p,q);(q,p)] th1 in      (* q \/ p |- p \/ q      *)
list_gen_rule_fd [p;q]
  (deduct_antisym_rule_fd th2 th1)
|> zipper
|> view
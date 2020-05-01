(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

exists_dist_disj_thm

([],"!P Q. (?(x:a). P x \/ Q x) <=> (?x. P x) \/ (?x. Q x)")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> disj_cases_rule_bk [0] [] [] "?(x:a). P x" "?(x:a). Q x"
|> assume_rule_bk
|> choose_rule_bk [0] [] 0 ("x:a","x:a")
|> assume_rule_bk
|> exists_rule_bk "x:a"
|> disj1_rule_bk
|> assume_rule_bk
|> choose_rule_bk [0] [] 0 ("x:a","x:a")
|> assume_rule_bk
|> exists_rule_bk "x:a"
|> disj2_rule_bk
|> assume_rule_bk
|> choose_rule_bk [0] [] 0 ("x:a","x:a")
|> assume_rule_bk
//|> focus_goal
|> disj_cases_rule_bk [0] [] [] "(P:a->bool) x" "(Q:a->bool) x"
|> assume_rule_bk
|> disj1_rule_bk
|> exists_rule_bk "x:a"
|> assume_rule_bk
|> disj2_rule_bk
|> exists_rule_bk "x:a"
|> assume_rule_bk
|> view
|> root
|> linearizeProof

let px = (parse_term(@"(P:'a->bool) x")) 
let qx = (parse_term(@"(Q:'a->bool) x")) 
let x = (parse_term(@"x:'a"))  in
let tm1 = (parse_term(@"?(x:'a). P x")) 
let tm2 = (parse_term(@"?(x:'a). Q x")) in
list_gen_rule [(parse_term(@"P:'a->bool"));(parse_term(@"Q:'a->bool"))]

(disj_cases_rule_fd (assume_rule_fd (parse_term(@"(?(x:'a). P x) \/ (?(x:'a). Q x)")))
  (* ?x. P x |- ?x. P x \/ Q x                     *)
  (choose_rule_fd x (assume_rule_fd tm1)
    (exists_rule_fd (parse_term(@"?(x:'a). P x \/ Q x")) x
      (disj1_rule_fd (assume_rule_fd px) qx) ))
  (* ?x. Q x |- ?x. P x \/ Q x                     *)
  (choose_rule_fd x (assume_rule_fd tm2)
    (exists_rule_fd (parse_term(@"?(x:'a). P x \/ Q x")) x
      (disj2_rule_fd px (assume_rule_fd qx)) )))
|> zipper
|> view

(deduct_antisym_rule_fd
  (* (?x. P x) \/ (?x. Q x) |- ?x. P x \/ Q x      *)
  (disj_cases_rule_fd (assume_rule_fd (parse_term(@"(?(x:'a). P x) \/ (?(x:'a). Q x)")))
    (* ?x. P x |- ?x. P x \/ Q x                     *)
    (choose_rule_fd x (assume_rule_fd tm1)
      (exists_rule_fd (parse_term(@"?(x:'a). P x \/ Q x")) x
        (disj1_rule_fd (assume_rule_fd px) qx) ))
    (* ?x. Q x |- ?x. P x \/ Q x                     *)
    (choose_rule_fd x (assume_rule_fd tm2)
      (exists_rule_fd (parse_term(@"?(x:'a). P x \/ Q x")) x
        (disj2_rule_fd px (assume_rule_fd qx)) )))
  (* ?x. P x \/ Q x |- (?x. P x) \/ (?x. Q x)      *)
  (choose_rule_fd x (assume_rule_fd (parse_term(@"?(x:'a). P x \/ Q x")))
    (* P x \/ Q x |- (?x. P x) \/ (?x. Q x)          *)
    (disj_cases_rule_fd (assume_rule_fd (parse_term(@"P (x:'a) \/ Q x")))
      (* P x |- (?x. P x) \/ (?x. Q x)                 *)
      (disj1_rule_fd (exists_rule_fd tm1 x (assume_rule_fd px)) tm2)
      (* Q x |- (?x. P x) \/ (?x. Q x)                 *)
      (disj2_rule_fd tm1 (exists_rule_fd tm2 x  (assume_rule_fd qx))) )))
|> zipper
|> view

(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

exists_null_thm

([],"!t. (?(x:a). t) <=> t")
|> start_proof
|> gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> exists_rule_bk "x:a"
|> assume_rule_bk
|> choose_rule_bk [0] [] 0 ("x:a","x:a")
|> assume_rule_bk
|> assume_rule_bk

|> view

skolem_thm

([],"!P. (!(x:a). ?(y:b). P x y) <=> (?f. !x. P x (f x))")
|> start_proof
|> gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> choose_rule_bk [0] [] 0 ("f:a->b","f:a->b")
|> assume_rule_bk
|> gen_rule_bk
|> exists_rule_bk "(f:a->b) x"
|> spec_rule_bk ("x:a","x:a") "!x. P x ((f:a->b) x)"
|> assume_rule_bk
|> focus_goal
//|> exists_rule_bk "(f:a->b)"
//|> gen_rule_bk
//|> focus_goal
//|> eq_mp_rule_bk [0] [0] "(f:a->b) x = y"

|> view











([],"!P a. (?(x:a). x = a /\ P x) <=> P a")
|> start_proof
|> gen_rule_bk
|> gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> exists_rule_bk "a:a"
|> conj_rule_bk [] [0]
|> refl_conv_bk
|> assume_rule_bk
//|> focus_goal
|> choose_rule_bk [0] [] 0 ("x:a","x:a")
|> assume_rule_bk
|> eq_mp_rule_bk [0] [0] "(P:a->bool) x"
|> mk_comb2_rule_bk
|> conjunct1_rule_bk "(P:a->bool) x"
|> assume_rule_bk
|> conjunct2_rule_bk "(x:a) = a"
|> assume_rule_bk

|> view

let tm = (parse_term(@"?(x:'a). x = a /\ P x"))
let s1 = assume_rule_fd (parse_term(@"(x:'a)=a /\ P x"))

(choose_rule_fd (parse_term(@"x:'a")) (assume_rule_fd tm)
    (eq_mp_rule_fd (mk_comb2_rule_fd (parse_term(@"P:'a->bool")) (conjunct1_rule_fd s1))
           (conjunct2_rule_fd s1)) )
|> zipper
|> view

gen_rule_fd (parse_term(@"P:'a->bool"))
 (gen_rule_fd (parse_term(@"a:'a"))
   (deduct_antisym_rule_fd
     (exists_rule_fd tm (parse_term(@"a:'a"))
       (conj_rule_fd (refl_conv_fd (parse_term(@"a:'a"))) (assume_rule_fd (parse_term(@"(P:'a->bool) a")))))
     (choose_rule_fd (parse_term(@"x:'a")) (assume_rule_fd tm)
       (eq_mp_rule_fd (mk_comb2_rule_fd (parse_term(@"P:'a->bool")) (conjunct1_rule_fd s1))
              (conjunct2_rule_fd s1)) )))
|> zipper
|> view


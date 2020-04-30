(**

*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

select_eq_thm

([],"!(a:'a). (@x. x = a) = a")
|> start_proof
|> gen_rule_bk
|> select_rule_bk "?(x:a). x = a"
|> exists_rule_bk "a:a"
|> refl_conv_bk

|> view

let a = (parse_term(@"a:'a"))

gen_rule_fd a
    (select_rule_fd
      (* |- ?x. x = a      *)
      (exists_rule_fd (parse_term(@"?(x:'a).x=a")) a (refl_conv_fd a)) )
|> zipper
|> view
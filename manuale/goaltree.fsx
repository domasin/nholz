#load "avvio.fsx"
open HOL

open System.IO

CoreThry.load
Equal.load
Bool.load


eq_mp_rule_fd
(* |- (\p. p) = (\p. p) <=> true  *)
    (sym_rule_fd (true_def |> thm_fd "true\_def"))
    (* |- (\p. p) = (\p. p)           *)
    (refl_conv_fd (parse_term(@"\(p:bool).p")))
|> zipper |> view |> loc_thm |> Option.get

// 0001 Truth
([],"true")
|> start_proof
|> eq_mp_rule_bk ("(\(p:bool). p) = \p. p" |> mkGoal [])
    |> sym_rule_bk
        |> by true_def "true\_def"                          |> lower |> prove |> right
    |> refl_conv_bk                                         |> lower |> prove |> lower |> prove
//|> view
|> loc_thm |> Option.get
|> fun x -> x = truth_thm

// 0003 not true
([],@"~ true <=> false")                                    |> start_proof
(* |- ~ true <=> false         *)
|> deduct_antisym_rule_bk [] []
    (* false |- ~ true             *)
    |> contr_rule_bk ("false" |> parse_term)           |> right
        |> assume_rule_bk                                   |> lower |> prove |> lower |> prove |> right
    (* ~ true |- false             *)
    |> eq_mp_rule_bk ("true" |> mkGoal [])
            (* ~ true |- true <=> false    *)
            |> eqf_intro_rule_bk
                |> assume_rule_bk                           |> lower |> prove |> lower |> prove |> right
            (* |- true  *)
            |> by truth_thm "truth\_thm"                    |> lower |> prove |> lower |> prove
//|> view
|> loc_thm |> Option.get
|> fun x -> x = not_true_thm

// 0004 not false
([],"~ false <=> true")
|> start_proof
|> deduct_antisym_rule_bk [] []
    |> add_asm_rule_bk ("true" |> parse_term)       |> right
        |> not_intro_rule_bk
            |> disch_rule_bk                        |> right
                |> assume_rule_bk                   |> lower |> prove |> lower |> prove |> lower |> prove |> lower |> prove |> right
|> add_asm_rule_bk ("~ false" |> parse_term)        |> right
    |> by truth_thm "truth\_thm"                    |> lower |> prove |> lower |> prove
//|> view
|> loc_thm |> Option.get
|> fun x -> x = not_false_thm




//// truth

//// forward classic
//(* |- true                        *)
//eq_mp_rule
//  (* |- (\p. p) = (\p. p) <=> true  *)
//  (sym_rule true_def)
//  (* |- (\p. p) = (\p. p)           *)
//  (refl_conv (parse_term(@"\(p:bool).p")))

//// forward with tree
//let th = 
//    (* |- true                        *)
//    eq_mp_rule_fd
//      (* |- (\p. p) = (\p. p) <=> true  *)
//      (sym_rule_fd (true_def |> thm_fd "true\_def"))
//      (* |- (\p. p) = (\p. p)           *)
//      (refl_conv_fd (parse_term(@"\(p:bool).p")))

//th |> zipper |> view



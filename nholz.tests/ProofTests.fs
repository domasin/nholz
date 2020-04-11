module ProofTests

//#I "./bin/Debug/netcoreapp3.1"
//#r "nholz.dll"
//open HOL
//fsi.AddPrinter print_type
//fsi.AddPrinter print_qtype
//fsi.AddPrinter print_term
//fsi.AddPrinter print_qterm
//fsi.AddPrinter print_thm

//#r "xunit.core.dll"
//#r "FsUnit.Xunit.dll"

open FsUnit.Xunit
open Xunit

open HOL

[<Fact>]
let ``truth_thm backward gives truth_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load   

    ([],"true")
    |> start_proof
    |> eq_mp_rule_bk ("(\(p:bool). p) = \p. p" |> mkGoal [])
        |> sym_rule_bk
            |> by true_def "true\_def"                          |> lower |> prove |> right
        |> refl_conv_bk                                         |> lower |> prove |> lower |> prove
    //|> view
    |> loc_thm |> Option.get
    |> fun x -> x = truth_thm
    |> should equal true

[<Fact>]
let ``truth_thm forward gives truth_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    //(* |- true                        *)
    eq_mp_rule_fd
        (* |- (\p. p) = (\p. p) <=> true  *)
        (sym_rule_fd (true_def |> thm_fd "true\_def"))
        (* |- (\p. p) = (\p. p)           *)
        (refl_conv_fd (parse_term(@"\(p:bool).p")))
    |> zipper |> loc_thm |> Option.get
    |> fun x -> x = truth_thm
    |> should equal true

[<Fact>]
let ``not_true_thm backward gives not_true_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    ([],@"~ true <=> false")                                    |> start_proof
    (* |- ~ true <=> false         *)
    |> deduct_antisym_rule_bk [] []
        (* false |- ~ true             *)
        |> contr_rule_bk                                        |> right
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
    |> should equal true

[<Fact>]
let ``not_true_thm forward gives not_true_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    (* |- ~ true <=> false         *)
    deduct_antisym_rule_fd
        (* false |- ~ true             *)
        (contr_rule_fd (parse_term(@"~ true")) (assume_rule_fd (parse_term(@"false"))))
        (* ~ true |- false             *)
        (eq_mp_rule_fd
            (* ~ true |- true <=> false    *)
            (eqf_intro_rule_fd (assume_rule_fd (parse_term(@"~ true"))))
            (truth_thm |> thm_fd "truth\_thm") )
    |> zipper |> loc_thm |> Option.get
    |> fun x -> x = not_true_thm
    |> should equal true

[<Fact>]
let ``not_false_thm backward gives not_false_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

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
    |> should equal true

//[<Fact>]
//let ``not_false_thm forward gives not_false_thm`` () =
//    let _t1 = CoreThry.load   
//    let _t2 = Equal.load      
//    let _t3 = Bool.load 

//    (* |- ~ true <=> false         *)
//    deduct_antisym_rule_fd
//        (* false |- ~ true             *)
//        (contr_rule_fd (parse_term(@"~ true")) (assume_rule_fd (parse_term(@"false"))))
//        (* ~ true |- false             *)
//        (eq_mp_rule_fd
//            (* ~ true |- true <=> false    *)
//            (eqf_intro_rule_fd (assume_rule_fd (parse_term(@"~ true"))))
//            (truth_thm |> thm_fd "truth\_thm") )
//    |> zipper |> loc_thm |> Option.get
//    |> fun x -> x = not_true_thm
//    |> should equal true
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
    (* |- true                        *)
    |> eq_mp_rule_bk [] [] "(\(p:bool). p) = \p. p"
        (* |- (\p. p) = (\p. p) <=> true  *)
        |> sym_rule_bk
            (* |- true <=> (\(p:bool). p) = (\p. p) *)
            |> by true_def "true\_def"
        (* |- (\p. p) = (\p. p)           *)
        |> refl_conv_bk
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
let ``fun_eq_thm backward gives fun_eq_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load   

    ([],@"!(f:'a->'b) g. f = g <=> (!x. f x = g x)") 
    |> start_proof
    |> list_gen_rule_bk
        |> deduct_antisym_rule_bk [] []
            |> trans_rule_bk "(\x. (g:'a->'b) x)"
                |> trans_rule_bk "(\x. (f:'a->'b) x)"
                    |> add_asm_rule_bk 0
                        |> sym_rule_bk
                        |> eta_conv_bk
                    |> mk_abs_rule_bk
                        |> spec_rule_bk ("x:'a","x:'a") "!(x:a). (f:a->b) x = g x"
                            |> assume_rule_bk
                |> add_asm_rule_bk 0
                    |> eta_conv_bk
            |> gen_rule_bk
                |> mk_comb1_rule_bk
                    |> assume_rule_bk
    //|> view
    |> loc_thm |> Option.get
    |> fun x -> x = fun_eq_thm
    |> should equal true

[<Fact>]
let ``fun_eq_thm forward gives fun_eq_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    let x = parse_term(@"x:'a") 
    let f = parse_term(@"f:'a->'b")
    let g = parse_term(@"g:'a->'b")
    
    (* |- !f g. f = g <=> (!x. f x = g x) *)
    (list_gen_rule_fd [f;g]
      (deduct_antisym_rule_fd
        (* !x. f x = g x |- f = g                 *)
        (list_trans_rule_fd
           [ (*               |- f = (\x. f x)      *)
             sym_rule_fd (eta_conv_fd (parse_term(@"\x. (f:'a->'b) x")));
             (* !x. f x = g x |- ... = (\x. g x)    *)
             mk_abs_rule_fd x
               (spec_rule_fd x (assume_rule_fd (parse_term(@"!x. (f:'a->'b) x = g x"))));
             (*               |- ... = g            *)
             eta_conv_fd (parse_term(@"\x. (g:'a->'b) x")) 
             ])
        (* f = g |- !x. f x = g x                 *)
        (gen_rule_fd x
          (mk_comb1_rule_fd (assume_rule_fd (parse_term(@"(f:'a->'b)=g"))) x) )))
    |> zipper
    |> loc_thm |> Option.get
    |> fun x -> x = fun_eq_thm
    |> should equal true

[<Fact>]
let ``not_true_thm backward gives not_true_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    ([],@"~ true <=> false")                                    
    |> start_proof
    (* |- ~ true <=> false         *)
    |> deduct_antisym_rule_bk [] []
        (* false |- ~ true             *)
        |> contr_rule_bk                                        
            |> assume_rule_bk
        (* ~ true |- false             *)
        |> eq_mp_rule_bk [0] [] "true"
                (* ~ true |- true <=> false    *)
                |> eqf_intro_rule_bk
                    |> assume_rule_bk
                (* |- true  *)
                |> by truth_thm "truth\_thm"
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
        |> add_asm_rule_bk 0
            |> not_intro_rule_bk
                |> disch_rule_bk                        
                    |> assume_rule_bk
        |> add_asm_rule_bk 0       
            |> by truth_thm "truth\_thm"
    //|> view
    |> loc_thm |> Option.get
    |> fun x -> x = not_false_thm
    |> should equal true

[<Fact>]
let ``not_false_thm forward gives not_false_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    //(* |- ~ false <=> true         *)
    deduct_antisym_rule_fd
      (* |- ~ false            *)
      (not_intro_rule_fd (disch_rule_fd (parse_term(@"false")) (assume_rule_fd (parse_term(@"false")))))
      (* |- true               *)
      (truth_thm |> thm_fd "truth\_thm")
    |> zipper |> loc_thm |> Option.get
    |> fun x -> x = not_false_thm
    |> should equal true

[<Fact>]
let ``true_not_eq_false_thm backward gives true_not_eq_false_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    ([],"~ (true <=> false)")
    |> start_proof
    |> eqf_elim_rule_bk
        |> deduct_antisym_rule_bk [] []
            (* false |- true <=> false         *)
            |> sym_rule_bk
                |> eqt_intro_rule_bk
                    |> assume_rule_bk
            (* true <=> false |- false         *)
            |> eq_mp_rule_bk [0] [] "true"
                |> assume_rule_bk
                    //|> add_asm_rule_bk 0
                |> by truth_thm "truth\_thm"
    //|> view
    |> loc_thm |> Option.get
    |> fun x -> x = true_not_eq_false_thm
    |> should equal true

[<Fact>]
let ``true_not_eq_false_thm forward gives true_not_eq_false_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    eqf_elim_rule_fd
        (deduct_antisym_rule_fd
              (* false |- true <=> false         *)
              (sym_rule_fd 
                (eqt_intro_rule_fd 
                    (assume_rule_fd (parse_term(@"false")))))
              (* true <=> false |- false         *)
              (eq_mp_rule_fd 
                (assume_rule_fd(parse_term(@"true <=> false"))) 
                    (truth_thm |> thm_fd "truth\_thm") ) )
    |> zipper 
    |> loc_thm |> Option.get
    |> fun x -> x = true_not_eq_false_thm
    |> should equal true

[<Fact>]
let ``not_dist_disj_thm backward gives not_dist_disj_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

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
    //|> view
    |> loc_thm |> Option.get
    |> fun x -> x = not_dist_disj_thm
    |> should equal true

[<Fact>]
let ``not_dist_disj_thm forward gives not_dist_disj_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

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
    |> loc_thm |> Option.get
    |> fun x -> x = not_dist_disj_thm
    |> should equal true

[<Fact>]
let ``conj_id_thm backward gives conj_id_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    ([],"!p. p /\ true <=> p")
    |> start_proof
    |> gen_rule_bk
    |> deduct_antisym_rule_bk [] []
    |> conj_rule_bk [0] []
    |> assume_rule_bk
    |> by truth_thm "truth_thm"
    |> conjunct1_rule_bk "true"
    |> assume_rule_bk
    //|> view
    |> loc_thm |> Option.get
    |> fun x -> x = conj_id_thm
    |> should equal true

[<Fact>]
let ``conj_id_thm forward gives conj_id_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    gen_rule_fd p
        (deduct_antisym_rule_fd
            (* p |- p /\ true *)
            (conj_rule_fd (p |> assume_rule_fd) (truth_thm |> thm_fd "truth_thm"))
            (* p /\ true |- p *)
            (conjunct1_rule_fd (@"p /\ true" |> parse_term |> assume_rule_fd))
        )
    |> zipper 
    |> loc_thm |> Option.get
    |> fun x -> x = conj_id_thm
    |> should equal true

[<Fact>]
let ``conj_zero_thm backward gives conj_zero_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    ([],"!p. p /\ false <=> false")
    |> start_proof
    |> gen_rule_bk
    |> deduct_antisym_rule_bk [] []
    |> contr_rule_bk
    |> assume_rule_bk
    |> conjunct2_rule_bk "p:bool"
    |> assume_rule_bk
    //|> view
    |> loc_thm |> Option.get
    |> fun x -> x = conj_zero_thm
    |> should equal true

[<Fact>]
let ``conj_zero_thm forward gives conj_zero_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    gen_rule_fd p
        (deduct_antisym_rule_fd
          (contr_rule_fd (parse_term(@"p /\ false")) (assume_rule_fd false_tm))
          (conjunct2_rule_fd (assume_rule_fd (parse_term(@"p /\ false")))) )
    |> zipper 
    |> loc_thm |> Option.get
    |> fun x -> x = conj_zero_thm
    |> should equal true

[<Fact>]
let ``conj_idem_thm backward gives conj_idem_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    ([],"!p. p /\ p <=> p")
    |> start_proof
    |> gen_rule_bk
    |> deduct_antisym_rule_bk [] []
    |> conj_rule_bk [0] [0]
    |> assume_rule_bk
    |> assume_rule_bk
    |> conjunct1_rule_bk "p:bool"
    |> assume_rule_bk
    //|> view
    |> loc_thm |> Option.get
    |> fun x -> x = conj_idem_thm
    |> should equal true

[<Fact>]
let ``conj_idem_thm forward gives conj_idem_thm`` () =
    let _t1 = CoreThry.load   
    let _t2 = Equal.load      
    let _t3 = Bool.load 

    gen_rule_fd p
        (deduct_antisym_rule_fd
          (conj_rule_fd (assume_rule_fd p) (assume_rule_fd p))
          (conjunct1_rule_fd (assume_rule_fd (parse_term(@"p /\ p")))) )
    |> zipper 
    |> loc_thm |> Option.get
    |> fun x -> x = conj_idem_thm
    |> should equal true


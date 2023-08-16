namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System.Numerics

module PretermTests = 

    (* dest_tyvar_pretype tests *)

    [<Fact>]
    let ``dest_tyvar_pretype_test``() =

        dest_tyvar_pretype (Ptyvar "num")
        |> should equal "num"

    (* dest_gtyvar_pretype tests *)

    [<Fact>]
    let ``dest_gtyvar_pretype_test``() =

        dest_gtyvar_pretype (Ptygvar 2)
        |> should equal 2

    (* is_gtyvar_pretype tests *)

    [<Fact>]
    let ``is_gtyvar_pretype_test``() =

        is_gtyvar_pretype (Ptygvar 2)
        |> should equal true

    (* mk_bin_pretype tests *)

    [<Fact>]
    let ``mk_bin_pretype_test``() =

        mk_bin_pretype ("+",Ptyvar "num",Ptyvar "num")
        |> should equal (Ptycomp ("+", [Ptyvar "num";Ptyvar "num"]))

    (* dest_infix_pretype tests *)

    [<Fact>]
    let ``dest_infix_pretype_test``() =
        //E' l'inverso di quella sopra ma richiede che sia definita una fixity per
        //l'operatore

        the_type_fixities.Value <- Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)

        let expected = ("+",Ptyvar "num",Ptyvar "num")
        let actual = dest_infix_pretype (Ptycomp ("+", [Ptyvar "num";Ptyvar "num"])) 

        the_type_fixities.Value <- (dltree_empty : dltree<string,fixity>)

        actual
        |> should equal expected

    (* strip_infix_pretype0 tests *)

    [<Fact>]
    let ``strip_infix_pretype0_1_test``() =

        the_type_fixities.Value <- Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)

        let expected = [Ptyvar "num";Ptyvar "num"]
        let actual = strip_infix_pretype0 ("+",LeftAssoc) (Ptycomp ("+", [Ptyvar "num";Ptyvar "num"])) 

        the_type_fixities.Value <- (dltree_empty : dltree<string,fixity>)

        actual
        |> should equal expected

    //TODO: aggiungere altri test per altri tipi di fixity

    (* strip_infix_pretype tests *)

    [<Fact>]
    let ``strip_infix_pretype_test``() =

        the_type_fixities.Value <- Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)

        let expected = ("+",[Ptyvar "num";Ptyvar "num"])
        let actual = strip_infix_pretype (Ptycomp ("+", [Ptyvar "num";Ptyvar "num"])) 

        the_type_fixities.Value <- (dltree_empty : dltree<string,fixity>)

        actual
        |> should equal expected

    (* mk_fun_pretype tests *)

    [<Fact>]
    let ``mk_fun_pretype_test``() =

        let expected = Ptycomp ("->", [Ptyvar "num";Ptyvar "num"])
        let actual = mk_fun_pretype (Ptyvar "num",Ptyvar "num")

        actual
        |> should equal expected

    (* dest_fun_pretype tests *)

    [<Fact>]
    let ``dest_fun_pretype_test``() =

        let expected = (Ptyvar "num",Ptyvar "num")
        let actual = dest_fun_pretype (Ptycomp ("->", [Ptyvar "num";Ptyvar "num"]))

        actual
        |> should equal expected

    (* type_to_pretype tests *)

    [<Fact>]
    let ``type_to_pretype_test``() =

        type_to_pretype (Tycomp ("B",[Tyvar "A"; Tyvar "C"]))
        |> should equal (Ptycomp ("B",[Ptyvar "A"; Ptyvar "C"]))

    (* pretype_to_type tests *)

    [<Fact>]
    let ``pretype_to_type_test``() =

        the_tyconsts.Value <- Node (1,("->",BigInteger.Parse "2"),Leaf,Leaf)

        let expected = Tycomp ("->",[Tyvar "A"; Tyvar "C"])
        let actual = pretype_to_type (Ptycomp ("->",[Ptyvar "A"; Ptyvar "C"]))

        the_tyconsts.Value <- (dltree_empty : dltree<string,BigInteger>)

        actual
        |> should equal expected

    (* pretype_tyvars tests *)

    [<Fact>]
    let ``pretype_tyvars_test``() =

        pretype_tyvars (Ptycomp ("fun", [Ptyvar "a"]))
        |> should equal ([Ptyvar "a"])

    (* pretype_gtyvars tests *)

    [<Fact>]
    let ``pretype_gtyvars_test``() =

        pretype_gtyvars (Ptycomp ("fun", [Ptygvar 0]))
        |> should equal ([Ptygvar 0])

    (* pretype_has_gtyvars tests *)

    [<Fact>]
    let ``pretype_has_gtyvars_false_test``() =

        pretype_has_gtyvars (Ptycomp ("fun", [Ptyvar "a"]))
        |> should equal false

    [<Fact>]
    let ``pretype_has_gtyvars_true_test``() =

        pretype_has_gtyvars (Ptycomp ("fun", [Ptygvar 0]))
        |> should equal true

    (* pretype_inst tests *)

    [<Fact>]
    let ``pretype_inst_test``() = 
        
        pretype_inst [(Ptyvar "a",Ptycomp ("bool",[]))] (Ptycomp("->",[Ptyvar "a";Ptycomp("bool",[])]))
        |> should equal (Ptycomp("->",[Ptycomp("bool",[]);Ptycomp("bool",[])]))

    (* pretype_complexity tests *)

    [<Fact>]
    let ``pretype_complexity_1_test``() = 
        
        pretype_complexity (Ptycomp("->",[Ptyvar "a";Ptycomp("bool",[])]))
        |> should equal 3 //2 Ptycomp + 1 Ptyvar 

    [<Fact>]
    let ``pretype_complexity_2_test``() = 
        
        pretype_complexity (Ptycomp("->",[Ptyvar "a";Ptycomp("->",[Ptyvar "a";Ptycomp("bool",[])])]))
        |> should equal 5 //3 Ptycomp + 2 Ptyvar

    (* mk_null_var_preterm tests *)

    [<Fact>]
    let ``mk_null_var_preterm_test``() = 
        
        mk_null_var_preterm "x"
        |> should equal (Ptmvar ("x", Ptygvar 0))

    (* dest_var_preterm tests *)

    [<Fact>]
    let ``dest_var_preterm_test``() = 
        
        dest_var_preterm (Ptmvar ("x", Ptygvar 0))
        |> should equal ("x", Ptygvar 0)

    (* mk_null_const_preterm tests *)

    [<Fact>]
    let ``mk_null_const_preterm_test``() = 
        
        mk_null_const_preterm "x"
        |> should equal (Ptmconst ("x", Ptygvar 0))

    (* const_preterm_name tests *)

    [<Fact>]
    let ``const_preterm_name_test``() = 
        
        const_preterm_name (Ptmconst ("x", Ptygvar 0))
        |> should equal "x"

    (* mk_comb_preterm tests *)

    [<Fact>]
    let ``mk_comb_preterm_test``() =

        let func = Ptmconst ("toString", Ptycomp ("->",[Ptyvar "num";Ptyvar "string"]))
        let constant = Ptmconst ("1", Ptyvar "num")
        let funcApp = Ptmcomb (func, constant)

        mk_comb_preterm (func, constant)
        |> should equal funcApp

    (* list_mk_comb_preterm tests *)

    [<Fact>]
    let ``list_mk_comb_preterm_test``() =

        list_mk_comb_preterm (Ptmconst ("toString", Ptycomp ("->",[Ptyvar "w";Ptyvar "z"])),[(Ptmconst ("a", Ptyvar "w"))])
        |> should equal (Ptmcomb ((Ptmconst ("toString", Ptycomp ("->",[Ptyvar "w";Ptyvar "z"]))),(Ptmconst ("a", Ptyvar "w"))))

    (* dest_comb_preterm tests *)

    [<Fact>]
    let ``dest_comb_preterm_test``() =

        //E' l'inversa di mk_comb_preterm

        let func = Ptmconst ("toString", Ptycomp ("->",[Ptyvar "num";Ptyvar "string"]))
        let constant = Ptmconst ("1", Ptyvar "num")
        let funcApp = Ptmcomb (func, constant)

        dest_comb_preterm funcApp
        |> should equal (func, constant)

    (* strip_comb_preterm tests *)

    [<Fact>]
    let ``strip_comb_pretermtest``() =

        //E' l'inversa di list_mk_comb_preterm

        strip_comb_preterm (Ptmcomb ((Ptmconst ("toString", Ptycomp ("->",[Ptyvar "w";Ptyvar "z"]))),(Ptmconst ("a", Ptyvar "w"))))
        |> should equal (Ptmconst ("toString", Ptycomp ("->",[Ptyvar "w";Ptyvar "z"])),[(Ptmconst ("a", Ptyvar "w"))])

    (* list_mk_abs_preterm tests *)

    [<Fact>]
    let ``list_mk_abs_preterm test``() =

        let var = Ptmvar ("x", Ptyvar "num")
        let trm = Ptmconst ("1", Ptyvar "num")
        let lambdaAbstr = Ptmabs (var, trm)

        list_mk_abs_preterm ([var],trm)
        |> should equal lambdaAbstr

    (* dest_abs_preterm tests *)

    [<Fact>]
    let ``dest_abs_preterm test``() =

        let var = Ptmvar ("x", Ptyvar "num")
        let trm = Ptmconst ("1", Ptyvar "num")
        let lambdaAbstr = Ptmabs (var, trm)

        dest_abs_preterm lambdaAbstr
        |> should equal (var,trm)

    (* strip_abs_preterm tests *)

    [<Fact>]
    let ``strip_abs_preterm test``() =

        //E' l'inversa di list_mk_abs_preterm

        let var = Ptmvar ("x", Ptyvar "num")
        let trm = Ptmconst ("1", Ptyvar "num")
        let lambdaAbstr = Ptmabs (var, trm)

        strip_abs_preterm lambdaAbstr
        |> should equal ([var],trm)

    (* is_typed_preterm tests *)

    [<Fact>]
    let ``is_typed_preterm_test``() = 
        
        is_typed_preterm (Ptmtyped (Ptmvar ("x", Ptygvar 0), Ptyvar "num"))
        |> should equal true

    (* is_atom_preterm tests *)

    [<Fact>]
    let ``is_atom_preterm_Ptmvar_test``() = 
        
        is_atom_preterm (Ptmvar ("x", Ptygvar 0))
        |> should equal true

    [<Fact>]
    let ``is_atom_preterm_Ptmconst_test``() = 
        
        is_atom_preterm (Ptmconst ("a", Ptyvar "w"))
        |> should equal true

    [<Fact>]
    let ``is_atom_preterm_Ptmtyped_test``() = 
        
        is_atom_preterm (Ptmtyped (Ptmvar ("x", Ptygvar 0), Ptyvar "num"))
        |> should equal true

    (* atom_preterm_name tests *)

    [<Fact>]
    let ``atom_preterm_name_Ptmconst_test``() = 
        
        atom_preterm_name (Ptmconst ("a", Ptyvar "w"))
        |> should equal "a"

    (* same_atom_preterm tests *)

    [<Fact>]
    let ``same_atom_preterm_test``() = 
        
        same_atom_preterm (Ptmconst ("a", Ptyvar "w")) (Ptmconst ("a", Ptyvar "w"))
        |> should equal true

    (* mk_bin_preterm tests *)

    [<Fact>]
    let ``mk_bin_preterm_test``() =

        let expected = 
            Ptmcomb (
                Ptmcomb (
                    Ptmconst ("toString", Ptycomp ("->",[Ptyvar "a";Ptycomp ("->",[Ptyvar "b";Ptyvar "c"])])), 
                    Ptmconst ("a", Ptyvar "a")
                ), 
                Ptmconst ("b", Ptyvar "b")
            )

        let actual = 
            mk_bin_preterm (
                Ptmconst ("toString", Ptycomp ("->",[Ptyvar "a";Ptycomp ("->",[Ptyvar "b";Ptyvar "c"])])), 
                Ptmconst ("a", Ptyvar "a"), 
                Ptmconst ("b", Ptyvar "b")
            )

        actual
        |> should equal expected

    (* list_mk_bin_preterm tests *)

    [<Fact>]
    let ``list_mk_bin_preterm_RightAssoc_test``() =

        //controllare questi unit test con concrete funzioni che associano a destra o a sinistra: i seguenti test non sono significativi

        let expected = 
            Ptmcomb (
                Ptmcomb (
                    Ptmconst ("toString", Ptycomp ("->",[Ptyvar "a";Ptycomp ("->",[Ptyvar "b";Ptyvar "c"])])), 
                    Ptmconst ("a", Ptyvar "a")
                ), 
                Ptmconst ("b", Ptyvar "b")
            )

        let actual = 
            list_mk_bin_preterm RightAssoc (Ptmconst ("toString", Ptycomp ("->",[Ptyvar "a";Ptycomp ("->",[Ptyvar "b";Ptyvar "c"])])))
                [Ptmconst ("a", Ptyvar "a");Ptmconst ("b", Ptyvar "b")]

        actual
        |> should equal expected

    [<Fact>]
    let ``list_mk_bin_preterm_LeftAssoc_test``() =

        //controllare questi unit test con concrete funzioni che associano a destra o a sinistra: i seguenti test non sono significativi

        let expected = 
            Ptmcomb (
                Ptmcomb (
                    Ptmconst ("toString", Ptycomp ("->",[Ptycomp ("->",[Ptyvar "a";Ptyvar "b"]);Ptyvar "c"])), 
                    Ptmconst ("a", Ptyvar "a")
                ), 
                Ptmconst ("b", Ptyvar "b")
            )

        let actual = 
            list_mk_bin_preterm LeftAssoc (Ptmconst ("toString", Ptycomp ("->",[Ptycomp ("->",[Ptyvar "a";Ptyvar "b"]);Ptyvar "c"])))
                [Ptmconst ("a", Ptyvar "a");Ptmconst ("b", Ptyvar "b")]

        actual
        |> should equal expected

    (* dest_bin_preterm tests *)

    [<Fact>]
    let ``dest_bin_preterm_test``() =

        //E' l'inversa di mk_bin_preterm

        let expected = 
                (
                    Ptmconst ("toString", Ptycomp ("->",[Ptyvar "a";Ptycomp ("->",[Ptyvar "b";Ptyvar "c"])])), 
                    Ptmconst ("a", Ptyvar "a"), 
                    Ptmconst ("b", Ptyvar "b")
                )

        let actual = 
            dest_bin_preterm (
                Ptmcomb (
                    Ptmcomb (
                        Ptmconst ("toString", Ptycomp ("->",[Ptyvar "a";Ptycomp ("->",[Ptyvar "b";Ptyvar "c"])])), 
                        Ptmconst ("a", Ptyvar "a")
                    ), 
                    Ptmconst ("b", Ptyvar "b")
                )
            )

        actual
        |> should equal expected

    (* strip_bin_preterm tests *)

    [<Fact>]
    let ``strip_bin_preterm_NonAssoc_test``() =

        //controllare questi unit test con concrete funzioni che associano a destra o a sinistra: i seguenti test non sono significativi
        //E' l'inversa di list_mk_bin_preterm

        let expected = [Ptmconst ("a", Ptyvar "a");Ptmconst ("b", Ptyvar "b")]
            
        let actual = 
            strip_bin_preterm LeftAssoc (Ptmconst ("toString", Ptycomp ("->",[Ptycomp ("->",[Ptyvar "a";Ptyvar "b"]);Ptyvar "c"])))
                (
                    Ptmcomb (
                        Ptmcomb (
                            Ptmconst ("toString", Ptycomp ("->",[Ptycomp ("->",[Ptyvar "a";Ptyvar "b"]);Ptyvar "c"])), 
                            Ptmconst ("a", Ptyvar "a")
                        ), 
                        Ptmconst ("b", Ptyvar "b")
                    )
                )

        actual
        |> should equal expected

    (* cond_fn tests *)

    [<Fact>]
    let ``cond_fn_test``() = 
        
        cond_fn
        |> should equal (Ptmconst ("COND", Ptygvar 0))

    (* mk_cond_preterm tests *)

    [<Fact>]
    let ``mk_cond_preterm_test``() =

        let expected = 
            Ptmcomb (
                Ptmcomb (
                    Ptmcomb (
                        Ptmconst ("COND", Ptygvar 0),
                        Ptmconst ("a", Ptyvar "w")
                    ),
                    Ptmconst ("b", Ptyvar "w")
                ),
                Ptmconst ("c", Ptyvar "w")
            )

        let actual = mk_cond_preterm (Ptmconst ("a", Ptyvar "w"),Ptmconst ("b", Ptyvar "w"),Ptmconst ("c", Ptyvar "w"))

        actual
        |> should equal expected

    (* dest_cond_preterm tests *)

    [<Fact>]
    let ``dest_cond_preterm_test``() =

        let expected = (Ptmconst ("a", Ptyvar "w"),Ptmconst ("b", Ptyvar "w"),Ptmconst ("c", Ptyvar "w"))
            

        let actual = dest_cond_preterm 
                        (
                            Ptmcomb (
                                Ptmcomb (
                                    Ptmcomb (
                                        Ptmconst ("COND", Ptygvar 0),
                                        Ptmconst ("a", Ptyvar "w")
                                    ),
                                    Ptmconst ("b", Ptyvar "w")
                                ),
                                Ptmconst ("c", Ptyvar "w")
                            )
                        )

        actual
        |> should equal expected

    (* is_cond_preterm tests *)

    [<Fact>]
    let ``is_cond_preterm_test``() =

        let expected = true
            

        let actual = is_cond_preterm 
                        (
                            Ptmcomb (
                                Ptmcomb (
                                    Ptmcomb (
                                        Ptmconst ("COND", Ptygvar 0),
                                        Ptmconst ("a", Ptyvar "w")
                                    ),
                                    Ptmconst ("b", Ptyvar "w")
                                ),
                                Ptmconst ("c", Ptyvar "w")
                            )
                        )

        actual
        |> should equal expected

    (* let_fn tests *)

    [<Fact>]
    let ``let_fn_test``() = 
        
        let_fn
        |> should equal (Ptmconst ("LET", Ptygvar 0))

    (* mk_let_preterm tests *)

    [<Fact>]
    let ``mk_let_preterm_test``() =

        // LET (\a. c) b
        let expected = 
            Ptmcomb (
                Ptmcomb (
                    Ptmconst ("LET", Ptygvar 0),
                    Ptmabs (
                        Ptmconst ("a", Ptyvar "w"),
                        Ptmconst ("c", Ptyvar "w")
                    )
                ),
                Ptmconst ("b", Ptyvar "w")
            )

        let actual = mk_let_preterm ([(Ptmconst ("a", Ptyvar "w"),Ptmconst ("b", Ptyvar "w"))], Ptmconst ("c", Ptyvar "w"))

        actual
        |> should equal expected

    (* dest_let_preterm tests *)

    [<Fact>]
    let ``dest_let_preterm_test``() =

        //E' l'inversa della precedente

        let expected = ([(Ptmconst ("a", Ptyvar "w"),Ptmconst ("b", Ptyvar "w"))], Ptmconst ("c", Ptyvar "w"))

        let actual = dest_let_preterm
                        (
                            Ptmcomb (
                                Ptmcomb (
                                    Ptmconst ("LET", Ptygvar 0),
                                    Ptmabs (
                                        Ptmconst ("a", Ptyvar "w"),
                                        Ptmconst ("c", Ptyvar "w")
                                    )
                                ),
                                Ptmconst ("b", Ptyvar "w")
                            )
                        )

        actual
        |> should equal expected

    (* is_let_preterm tests *)

    [<Fact>]
    let ``is_let_preterm_test``() =

        let expected = true

        let actual = is_let_preterm
                        (
                            Ptmcomb (
                                Ptmcomb (
                                    Ptmconst ("LET", Ptygvar 0),
                                    Ptmabs (
                                        Ptmconst ("a", Ptyvar "w"),
                                        Ptmconst ("c", Ptyvar "w")
                                    )
                                ),
                                Ptmconst ("b", Ptyvar "w")
                            )
                        )

        actual
        |> should equal expected

    (* pair_fn tests *)

    [<Fact>]
    let ``pair_fn_test``() = 
        
        pair_fn
        |> should equal (Ptmconst ("PAIR", Ptygvar 0))

    (* mk_pair_preterm tests *)

    [<Fact>]
    let ``mk_pair_preterm_test``() =

        let expected = 
            Ptmcomb (
                Ptmcomb (
                    Ptmconst ("PAIR", Ptygvar 0),
                    Ptmconst ("a", Ptyvar "w")
                ),
                Ptmconst ("b", Ptyvar "w")
            )

        let actual = mk_pair_preterm (Ptmconst ("a", Ptyvar "w"),Ptmconst ("b", Ptyvar "w"))

        actual
        |> should equal expected

    (* list_mk_pair_preterm tests *)

    [<Fact>]
    let ``list_mk_pair_preterm_test``() =

        //Nota qui l'associazione a destra e riprogetta gli unit test per list_mk_bin_preterm

        let expected = 
            Ptmcomb (
                Ptmcomb (
                        Ptmconst ("PAIR", Ptygvar 0),
                        Ptmconst ("a", Ptyvar "w")
                ),
                Ptmcomb (
                    Ptmcomb (
                        Ptmconst ("PAIR", Ptygvar 0),
                        Ptmconst ("b", Ptyvar "w")
                    ),
                    Ptmconst ("c", Ptyvar "w")
                )
            )

        let actual = list_mk_pair_preterm [Ptmconst ("a", Ptyvar "w");Ptmconst ("b", Ptyvar "w");Ptmconst ("c", Ptyvar "w")]

        actual
        |> should equal expected

    (* strip_pair_preterm tests *)

    [<Fact>]
    let ``strip_pair_preterm_test``() =

        //Nota qui l'associazione a destra e riprogetta gli unit test per strip_bin_preterm

        let expected = [Ptmconst ("a", Ptyvar "w");Ptmconst ("b", Ptyvar "w");Ptmconst ("c", Ptyvar "w")]
            
        let actual = strip_pair_preterm 
                        (
                            Ptmcomb (
                                Ptmcomb (
                                        Ptmconst ("PAIR", Ptygvar 0),
                                        Ptmconst ("a", Ptyvar "w")
                                ),
                                Ptmcomb (
                                    Ptmcomb (
                                        Ptmconst ("PAIR", Ptygvar 0),
                                        Ptmconst ("b", Ptyvar "w")
                                    ),
                                    Ptmconst ("c", Ptyvar "w")
                                )
                            )
                        )

        actual
        |> should equal expected

    (* is_pair_preterm tests *)

    [<Fact>]
    let ``is_pair_preterm_test``() =

        let expected = true
            
        let actual = is_pair_preterm 
                        (
                            Ptmcomb (
                                Ptmcomb (
                                        Ptmconst ("PAIR", Ptygvar 0),
                                        Ptmconst ("a", Ptyvar "w")
                                ),
                                Ptmcomb (
                                    Ptmcomb (
                                        Ptmconst ("PAIR", Ptygvar 0),
                                        Ptmconst ("b", Ptyvar "w")
                                    ),
                                    Ptmconst ("c", Ptyvar "w")
                                )
                            )
                        )

        actual
        |> should equal expected

    (* numeral_fn tests *)

    [<Fact>]
    let ``numeral_fn_test``() = 
        
        numeral_fn
        |> should equal (Ptmconst ("NUMERAL", Ptygvar 0))

    (* mk_bigint_nat_preterm tests *)

    [<Fact>]
    let ``mk_bigint_nat_preterm_0_test``() =

        let expected = 
            Ptmcomb (
                Ptmconst ("NUMERAL", Ptygvar 0),
                Ptmconst ("ZERO", Ptygvar 0)
            )

        let actual = mk_bigint_nat_preterm (BigInteger.Parse "0")

        actual
        |> should equal expected

    [<Fact>]
    let ``mk_bigint_nat_preterm_1_test``() =

        let expected = 
            Ptmcomb (
                Ptmconst ("NUMERAL", Ptygvar 0),
                Ptmcomb (
                    Ptmconst ("BIT1", Ptygvar 0),
                    Ptmconst ("ZERO", Ptygvar 0)
                )
            )

        let actual = mk_bigint_nat_preterm (BigInteger.Parse "1")

        actual
        |> should equal expected

    [<Fact>]
    let ``mk_bigint_nat_preterm_2_test``() =

        let expected = 
            Ptmcomb (
                Ptmconst ("NUMERAL", Ptygvar 0),
                Ptmcomb (
                    Ptmconst ("BIT0", Ptygvar 0),
                    Ptmcomb (
                        Ptmconst ("BIT1", Ptygvar 0),
                        Ptmconst ("ZERO", Ptygvar 0)
                    )
                )
            )

        let actual = mk_bigint_nat_preterm (BigInteger.Parse "2")

        actual
        |> should equal expected

    [<Fact>]
    let ``mk_bigint_nat_preterm_3_test``() =

        let expected = 
            Ptmcomb (
                Ptmconst ("NUMERAL", Ptygvar 0),
                Ptmcomb (
                    Ptmconst ("BIT1", Ptygvar 0),
                    Ptmcomb (
                        Ptmconst ("BIT1", Ptygvar 0),
                        Ptmconst ("ZERO", Ptygvar 0)
                    )
                )
            )

        let actual = mk_bigint_nat_preterm (BigInteger.Parse "3")

        actual
        |> should equal expected

    [<Fact>]
    let ``mk_bigint_nat_preterm_4_test``() =

        let expected = 
            Ptmcomb (
                Ptmconst ("NUMERAL", Ptygvar 0),
                Ptmcomb (
                    Ptmconst ("BIT0", Ptygvar 0),
                    Ptmcomb (
                            Ptmconst ("BIT0", Ptygvar 0),
                            Ptmcomb (
                                Ptmconst ("BIT1", Ptygvar 0),
                                Ptmconst ("ZERO", Ptygvar 0)
                            )
                    )
                )
            )

        let actual = mk_bigint_nat_preterm (BigInteger.Parse "4")

        actual
        |> should equal expected

    (* dest_bigint_nat_preterm tests *)

    [<Fact>]
    let ``dest_bigint_nat_preterm_4_test``() =

        let expected = (BigInteger.Parse "4")
            
        let actual = dest_bigint_nat_preterm 
                        (
                            Ptmcomb (
                                Ptmconst ("NUMERAL", Ptygvar 0),
                                Ptmcomb (
                                    Ptmconst ("BIT0", Ptygvar 0),
                                    Ptmcomb (
                                            Ptmconst ("BIT0", Ptygvar 0),
                                            Ptmcomb (
                                                Ptmconst ("BIT1", Ptygvar 0),
                                                Ptmconst ("ZERO", Ptygvar 0)
                                            )
                                    )
                                )
                            )
                        )

        actual
        |> should equal expected

    (* is_nat_preterm tests *)

    [<Fact>]
    let ``is_nat_preterm_test``() =

        let expected = true
            
        let actual = is_nat_preterm 
                        (
                            Ptmcomb (
                                Ptmconst ("NUMERAL", Ptygvar 0),
                                Ptmcomb (
                                    Ptmconst ("BIT0", Ptygvar 0),
                                    Ptmcomb (
                                            Ptmconst ("BIT0", Ptygvar 0),
                                            Ptmcomb (
                                                Ptmconst ("BIT1", Ptygvar 0),
                                                Ptmconst ("ZERO", Ptygvar 0)
                                            )
                                    )
                                )
                            )
                        )

        actual
        |> should equal expected

    (* mk_enum_preterm tests *)

    [<Fact>]
    let ``mk_enum_preterm_test``() =

        the_enum_db.Value <- Node (1,("NIL",("CONS",("{","}"))),Leaf,Leaf)
        the_enum_brackets.Value <- Node (1,("{","NIL"),Node (1,("}","NIL"),Leaf,Leaf),Node (1,("{}","NIL"),Leaf,Leaf))

        let expected = 
            Ptmcomb (
                Ptmcomb (
                    Ptmconst ("CONS", Ptygvar 0),
                    Ptmconst ("a", Ptygvar 0)
                ),
                Ptmcomb (
                    Ptmcomb (
                        Ptmconst ("CONS", Ptygvar 0),
                        Ptmconst ("b", Ptygvar 0)
                    ),
                    Ptmcomb (
                        Ptmcomb (
                            Ptmconst ("CONS", Ptygvar 0),
                            Ptmconst ("c", Ptygvar 0)
                        ),
                        Ptmconst ("NIL", Ptygvar 0)
                    )
                )
            )

        let actual = mk_enum_preterm ("{", [ Ptmconst ("a", Ptygvar 0); Ptmconst ("b", Ptygvar 0); Ptmconst ("c", Ptygvar 0); ], "}")

        the_enum_brackets.Value <- (dltree_empty : dltree<string, string>)
        the_enum_db.Value <- (dltree_empty :  dltree<string, string * (string * string)>)

        actual
        |> should equal expected

    (* dest_enum_preterm tests *)

    // [<Fact>]
    let ``dest_enum_preterm_test``() =

        the_enum_db.Value <- Node (1,("NIL",("CONS",("{","}"))),Leaf,Leaf)
        the_enum_brackets.Value <- Node (1,("{","NIL"),Node (1,("}","NIL"),Leaf,Leaf),Node (1,("{}","NIL"),Leaf,Leaf))

        let expected = ("{", [ Ptmconst ("a", Ptygvar 0); Ptmconst ("b", Ptygvar 0); Ptmconst ("c", Ptygvar 0); ], "}")
            
        let actual = dest_enum_preterm 
                                    (
                                        Ptmcomb (
                                            Ptmcomb (
                                                Ptmconst ("CONS", Ptygvar 0),
                                                Ptmconst ("a", Ptygvar 0)
                                            ),
                                            Ptmcomb (
                                                Ptmcomb (
                                                    Ptmconst ("CONS", Ptygvar 0),
                                                    Ptmconst ("b", Ptygvar 0)
                                                ),
                                                Ptmcomb (
                                                    Ptmcomb (
                                                        Ptmconst ("CONS", Ptygvar 0),
                                                        Ptmconst ("c", Ptygvar 0)
                                                    ),
                                                    Ptmconst ("NIL", Ptygvar 0)
                                                )
                                            )
                                        )
                                    )

        the_enum_brackets.Value <- (dltree_empty : dltree<string, string>)
        the_enum_db.Value <- (dltree_empty :  dltree<string, string * (string * string)>)

        actual
        |> should equal expected

    (* is_enum_preterm tests *)

    [<Fact>]
    let ``is_enum_preterm_test``() =

        the_enum_db.Value <- Node (1,("NIL",("CONS",("{","}"))),Leaf,Leaf)
        the_enum_brackets.Value <- Node (1,("{","NIL"),Node (1,("}","NIL"),Leaf,Leaf),Node (1,("{}","NIL"),Leaf,Leaf))

        let expected = true
            
        let actual = is_enum_preterm 
                                    (
                                        Ptmcomb (
                                            Ptmcomb (
                                                Ptmconst ("CONS", Ptygvar 0),
                                                Ptmconst ("a", Ptygvar 0)
                                            ),
                                            Ptmcomb (
                                                Ptmcomb (
                                                    Ptmconst ("CONS", Ptygvar 0),
                                                    Ptmconst ("b", Ptygvar 0)
                                                ),
                                                Ptmcomb (
                                                    Ptmcomb (
                                                        Ptmconst ("CONS", Ptygvar 0),
                                                        Ptmconst ("c", Ptygvar 0)
                                                    ),
                                                    Ptmconst ("NIL", Ptygvar 0)
                                                )
                                            )
                                        )
                                    )

        the_enum_brackets.Value <- (dltree_empty : dltree<string, string>)
        the_enum_db.Value <- (dltree_empty :  dltree<string, string * (string * string)>)

        actual
        |> should equal expected

    (* strip_infix_preterm tests *)

    [<Fact>]
    let ``strip_infix_preterm_test``() =

        the_fixities.Value <- Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)


        let expected = 
                        (
                            Ptmconst ("+", Ptycomp ("->",[Ptygvar 0;Ptycomp ("->",[Ptygvar 0;Ptygvar 0])])), 
                            [Ptmconst ("1", Ptygvar 0); Ptmconst ("2", Ptygvar 0)]
                        )

        let actual = strip_infix_preterm
                        (
                            Ptmcomb (
                                Ptmcomb (
                                    Ptmconst ("+", Ptycomp ("->",[Ptygvar 0;Ptycomp ("->",[Ptygvar 0;Ptygvar 0])])), 
                                    Ptmconst ("1", Ptygvar 0)
                                ), 
                                Ptmconst ("2", Ptygvar 0)
                            )
                        )

        the_type_fixities.Value <- (dltree_empty : dltree<string,fixity>)

        actual
        |> should equal expected

    (* is_prefix_preterm tests *)

    [<Fact>]
    let ``is_prefix_preterm_true_test``() =

        the_fixities.Value <- Node (1,("~",Prefix),Leaf,Leaf)

        let expected = true

        let actual = is_prefix_preterm
                        (
                            Ptmcomb (
                                    Ptmconst ("~", Ptycomp ("->",[Ptygvar 0;Ptygvar 0])), 
                                    Ptmconst ("TRUE", Ptygvar 0)
                                )
                        )

        the_type_fixities.Value <- (dltree_empty : dltree<string,fixity>)

        actual
        |> should equal expected

    (* is_prefix_preterm tests *)

    [<Fact>]
    let ``is_prefix_preterm_false_test``() =

        the_fixities.Value <- Node (1,("~",Prefix),Leaf,Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf))

        let expected = false

        let actual = is_prefix_preterm
                        (
                            Ptmcomb (
                                Ptmcomb (
                                    Ptmconst ("+", Ptycomp ("->",[Ptygvar 0;Ptycomp ("->",[Ptygvar 0;Ptygvar 0])])), 
                                    Ptmconst ("1", Ptygvar 0)
                                ), 
                                Ptmconst ("2", Ptygvar 0)
                            )
                        )

        the_type_fixities.Value <- (dltree_empty : dltree<string,fixity>)

        actual
        |> should equal expected

    (* is_infix_preterm tests *)

    [<Fact>]
    let ``is_infix_preterm_test``() =

        the_fixities.Value <- Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)

        let expected = true

        let actual = is_infix_preterm
                        (
                            Ptmcomb (
                                Ptmcomb (
                                    Ptmconst ("+", Ptycomp ("->",[Ptygvar 0;Ptycomp ("->",[Ptygvar 0;Ptygvar 0])])), 
                                    Ptmconst ("1", Ptygvar 0)
                                ), 
                                Ptmconst ("2", Ptygvar 0)
                            )
                        )

        the_type_fixities.Value <- (dltree_empty : dltree<string,fixity>)

        actual
        |> should equal expected

    (* is_postfix_preterm tests *)

    [<Fact>]
    let ``is_postfix_preterm_true_test``() =

        the_fixities.Value <- Node (1,("~",Postfix),Leaf,Leaf)
        //TODO: cambiare con un operatore che di solito è postfisso

        let expected = true

        let actual = is_postfix_preterm
                        (
                            Ptmcomb (
                                    Ptmconst ("~", Ptycomp ("->",[Ptygvar 0;Ptygvar 0])), 
                                    Ptmconst ("TRUE", Ptygvar 0)
                                )
                        )

        the_type_fixities.Value <- (dltree_empty : dltree<string,fixity>)

        actual
        |> should equal expected

    (* mk_binder_preterm tests *)

    [<Fact>]
    let ``mk_binder_preterm_test``() =
        
        let expected = 
            Ptmcomb (
                Ptmconst ("f", Ptycomp ("->", [Ptycomp ("->", [Ptygvar 0; Ptygvar 0]); Ptygvar 0])), 
                Ptmabs (
                    Ptmvar ("x", Ptygvar 0), 
                    Ptmconst ("1", Ptygvar 0)
                )
            )

        let actual = mk_binder_preterm 
                        (
                            Ptmconst ("f", Ptycomp ("->",[Ptycomp ("->",[Ptygvar 0;Ptygvar 0]);Ptygvar 0])),
                            Ptmvar ("x", Ptygvar 0),
                            Ptmconst ("1", Ptygvar 0)
                        )

        actual
        |> should equal expected

    (* list_mk_binder_preterm tests *)

    [<Fact>]
    let ``list_mk_binder_preterm_test``() =
        
        let expected = 
            Ptmcomb (
                Ptmconst ("f", Ptycomp ("->", [Ptycomp ("->", [Ptygvar 0;Ptygvar 0]);Ptygvar 0])), 
                Ptmabs (
                    Ptmvar ("x", Ptygvar 0), 
                    Ptmcomb (
                        Ptmconst ("f", Ptycomp ("->", [Ptycomp ("->", [Ptygvar 0;Ptygvar 0]);Ptygvar 0])), 
                        Ptmabs (
                            Ptmvar ("y", Ptygvar 0), 
                            Ptmconst ("1", Ptygvar 0)
                        )
                    )
                )
            )
        let actual = list_mk_binder_preterm 
                        (
                            Ptmconst ("f", Ptycomp ("->",[Ptycomp ("->",[Ptygvar 0;Ptygvar 0]);Ptygvar 0])),
                            [Ptmvar ("x", Ptygvar 0);Ptmvar ("y", Ptygvar 0)],
                            Ptmconst ("1", Ptygvar 0)
                        )

        actual
        |> should equal expected

    (* dest_binder_preterm tests *)

    [<Fact>]
    let ``dest_binder_preterm_test``() =

        the_fixities.Value <- Node (1,("f",Binder),Leaf,Leaf)
        
        //E' l'inversa di mk_binder_preterm
        let expected =  
                        (
                            Ptmconst ("f", Ptycomp ("->",[Ptycomp ("->",[Ptygvar 0;Ptygvar 0]);Ptygvar 0])),
                            Ptmvar ("x", Ptygvar 0),
                            Ptmconst ("1", Ptygvar 0)
                        )

        let actual = dest_binder_preterm
                        (
                            Ptmcomb (
                                Ptmconst ("f", Ptycomp ("->",[Ptycomp ("->",[Ptygvar 0;Ptygvar 0]);Ptygvar 0])), 
                                Ptmabs (
                                    Ptmvar ("x", Ptygvar 0), 
                                    Ptmconst ("1", Ptygvar 0)
                                )
                            )
                        )

        the_fixities.Value <- (dltree_empty : dltree<string,fixity>)

        actual
        |> should equal expected

    (* strip_binder_preterm tests *)

    [<Fact>]
    let ``strip_binder_preterm_test``() =

        the_fixities.Value <- Node (1,("f",Binder),Leaf,Leaf)
        
        let expected = 
                        (
                            Ptmconst ("f", Ptycomp ("->",[Ptycomp ("->",[Ptygvar 0;Ptygvar 0]);Ptygvar 0])),
                            [Ptmvar ("x", Ptygvar 0);Ptmvar ("y", Ptygvar 0)],
                            Ptmconst ("1", Ptygvar 0)
                        )

        let actual = strip_binder_preterm
                        (
                            Ptmcomb (
                                Ptmconst ("f", Ptycomp ("->", [Ptycomp ("->", [Ptygvar 0;Ptygvar 0]);Ptygvar 0])), 
                                Ptmabs (
                                    Ptmvar ("x", Ptygvar 0), 
                                    Ptmcomb (
                                        Ptmconst ("f", Ptycomp ("->", [Ptycomp ("->", [Ptygvar 0;Ptygvar 0]);Ptygvar 0])), 
                                        Ptmabs (
                                            Ptmvar ("y", Ptygvar 0), 
                                            Ptmconst ("1", Ptygvar 0)
                                        )
                                    )
                                )
                            )
                        )

        the_fixities.Value <- (dltree_empty : dltree<string,fixity>)

        actual
        |> should equal expected

    (* is_binder_preterm tests *)

    [<Fact>]
    let ``is_binder_preterm_test``() =

        the_fixities.Value <- Node (1,("f",Binder),Leaf,Leaf)
        
        let expected = true

        let actual = is_binder_preterm
                        (
                            Ptmcomb (
                                Ptmconst ("f", Ptycomp ("->",[Ptycomp ("->",[Ptygvar 0;Ptygvar 0]);Ptygvar 0])), 
                                Ptmabs (
                                    Ptmvar ("x", Ptygvar 0), 
                                    Ptmconst ("1", Ptygvar 0)
                                )
                            )
                        )

        the_fixities.Value <- (dltree_empty : dltree<string,fixity>)

        actual
        |> should equal expected

    (* term_to_preterm tests *)

    [<Fact>]
    let ``term_to_preterm_equality_test``() =

        the_tyconsts.Value <- Node (1,("->",BigInteger.Parse "2"),Leaf,Leaf)
        the_consts.Value <- Node (1,("=",Tycomp ("->",[Tyvar "a";Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])])])),Leaf,Leaf) //defines equlity on generic types

        let expected = Ptmcomb (
                            Ptmcomb (
                                Ptmconst ("=", Ptycomp ("->", [Ptyvar ("num");Ptycomp ("->", [Ptyvar ("num");Ptycomp ("bool", [])])])), 
                                Ptmconst ("1", Ptyvar ("num"))
                            ), 
                            Ptmconst ("1", Ptyvar ("num"))
                        )

        let actual = term_to_preterm
                        (
                            Tmcomb (
                                Tmcomb (
                                    Tmconst ("=", Tycomp ("->", [Tyvar "num"; Tycomp ("->", [Tyvar "num"; Tycomp ("bool", [])])])),
                                    Tmconst ("1", Tyvar "num")), 
                                Tmconst ("1", Tyvar "num"))
                        )

        the_tyconsts.Value <- (dltree_empty : dltree<string,BigInteger>)
        the_consts.Value <- (dltree_empty : dltree<string,hol_type>)

        actual
        |> should equal expected

    [<Fact>]
    let ``term_to_preterm_equivalence_test``() =

        the_tyconsts.Value <- Node (1,("->",BigInteger.Parse "2"),Leaf,Leaf)
        the_consts.Value <- Node (1,("=",Tycomp ("->",[Tyvar "a";Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])])])),Leaf,Leaf) //defines equlity on generic types

        let expected = Ptmcomb (
                            Ptmcomb (
                                Ptmconst ("<=>", Ptycomp ("->", [Ptycomp ("bool", []);Ptycomp ("->", [Ptycomp ("bool", []);Ptycomp ("bool", [])])])), 
                                Ptmconst ("a", Ptycomp ("bool", []))
                            ), 
                            Ptmconst ("b", Ptycomp ("bool", []))
                        )

        let actual = term_to_preterm
                        (
                            Tmcomb (
                                Tmcomb (
                                    Tmconst ("=", Tycomp ("->", [Tycomp ("bool", []); Tycomp ("->", [Tycomp ("bool", []); Tycomp ("bool", [])])])),
                                    Tmconst ("a", Tycomp ("bool", []))), 
                                Tmconst ("b", Tycomp ("bool", [])))
                        )

        the_tyconsts.Value <- (dltree_empty : dltree<string,BigInteger>)
        the_consts.Value <- (dltree_empty : dltree<string,hol_type>)

        actual
        |> should equal expected

    (* preterm_tyvars tests *)

    [<Fact>]
    let ``preterm_tyvars_test``() =

        let expected = [Ptyvar ("num")]

        let actual = preterm_tyvars
                        (
                            Ptmcomb (
                                Ptmcomb (
                                    Ptmconst ("=", Ptycomp ("->", [Ptyvar ("num");Ptycomp ("->", [Ptyvar ("num");Ptycomp ("bool", [])])])), 
                                    Ptmconst ("1", Ptyvar ("num"))
                                ), 
                                Ptmconst ("1", Ptyvar ("num"))
                            )
                        )

        actual
        |> should equal expected

    (* preterm_gtyvars tests *)

    [<Fact>]
    let ``preterm_gtyvars_test``() =

        let expected = [Ptygvar 0]

        let actual = preterm_gtyvars
                        (
                            Ptmcomb (
                                Ptmcomb (
                                    Ptmconst ("=", Ptycomp ("->", [Ptygvar 0;Ptycomp ("->", [Ptygvar 0;Ptycomp ("bool", [])])])), 
                                    Ptmconst ("1", Ptygvar 0)
                                ), 
                                Ptmconst ("1", Ptygvar 0)
                            )
                        )

        actual
        |> should equal expected

    (* preterm_has_gtyvars tests *)

    [<Fact>]
    let ``preterm_has_gtyvars_test``() =

        let expected = true

        let actual = preterm_has_gtyvars
                        (
                            Ptmcomb (
                                Ptmcomb (
                                    Ptmconst ("=", Ptycomp ("->", [Ptygvar 0;Ptycomp ("->", [Ptygvar 0;Ptycomp ("bool", [])])])), 
                                    Ptmconst ("1", Ptygvar 0)
                                ), 
                                Ptmconst ("1", Ptygvar 0)
                            )
                        )

        actual
        |> should equal expected

    (* preterm_to_term tests *)

    [<Fact>]
    let ``preterm_to_term_equality_test``() =

        the_tyconsts.Value <- Node (1,("->",BigInteger.Parse "2"),Leaf,Node (1,("bool",BigInteger.Parse "0"),Leaf,Leaf))
        the_consts.Value <- Node (1,("=",Tycomp ("->",[Tyvar "a";Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])])])),Node (1,("1",Tyvar "num"),Leaf,Leaf),Leaf)

        let expected = 
                        (
                            Tmcomb (
                                Tmcomb (
                                    Tmconst ("=", Tycomp ("->", [Tyvar "num"; Tycomp ("->", [Tyvar "num"; Tycomp ("bool", [])])])),
                                    Tmconst ("1", Tyvar "num")), 
                                Tmconst ("1", Tyvar "num"))
                        )

        let actual = preterm_to_term 
                        (
                            Ptmcomb (
                                Ptmcomb (
                                    Ptmconst ("=", Ptycomp ("->", [Ptyvar ("num");Ptycomp ("->", [Ptyvar ("num");Ptycomp ("bool", [])])])), 
                                    Ptmconst ("1", Ptyvar ("num"))
                                ), 
                                Ptmconst ("1", Ptyvar ("num"))
                            )
                        )

        the_tyconsts.Value <- (dltree_empty : dltree<string,BigInteger>)
        the_consts.Value <- (dltree_empty : dltree<string,hol_type>)

        actual
        |> should equal expected

    (* preterm_inst tests *)

    [<Fact>]
    let ``preterm_inst_test``() = 
        
        preterm_inst 
            [(Ptygvar 0,Ptycomp ("bool",[]))] 
            (
                Ptmcomb (
                    Ptmcomb (
                        Ptmconst ("=", Ptycomp ("->", [Ptygvar 0;Ptycomp ("->", [Ptygvar 0;Ptycomp ("bool", [])])])), 
                        Ptmconst ("1", Ptygvar 0)
                    ), 
                    Ptmconst ("1", Ptygvar 0)
                )
            )

        |> should equal 
                    (
                        Ptmcomb (
                            Ptmcomb (
                                Ptmconst ("=", Ptycomp ("->", [Ptycomp ("bool", []);Ptycomp ("->", [Ptycomp ("bool", []);Ptycomp ("bool", [])])])), 
                                Ptmconst ("1", Ptycomp ("bool",[]))
                            ), 
                            Ptmconst ("1", Ptycomp ("bool",[]))
                        )
                    )

    (* preterm_pretype_match tests *)

    [<Fact>]
    let ``preterm_pretype_match_test``() = 
        
        //Nota che se si invertono i pretermini il match non è più eseguito: è giusto?
        preterm_pretype_match 
            (
                Ptmcomb (
                    Ptmcomb (
                        Ptmconst ("=", Ptycomp ("->", [Ptygvar 0;Ptycomp ("->", [Ptygvar 0;Ptycomp ("bool", [])])])), 
                        Ptmconst ("1", Ptygvar 0)
                    ), 
                    Ptmconst ("1", Ptygvar 0)
                ),
                Ptmcomb (
                    Ptmcomb (
                        Ptmconst ("=", Ptycomp ("->", [Ptycomp ("bool", []);Ptycomp ("->", [Ptycomp ("bool", []);Ptycomp ("bool", [])])])), 
                        Ptmconst ("1", Ptycomp ("bool",[]))
                    ), 
                    Ptmconst ("1", Ptycomp ("bool",[]))
                )
            )
        |> should equal [(Ptygvar 0,Ptycomp ("bool",[]))]
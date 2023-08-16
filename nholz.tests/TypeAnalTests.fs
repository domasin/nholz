namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System.Numerics

module TypeAnalTests = 
    (* pretype_ok tests *)

    [<Fact>]
    let ``pretype_ok_test``() =

        the_tyconsts.Value <- Node (1,("->",BigInteger.Parse "2"),Leaf,Node (1,("bool",BigInteger.Parse "0"),Leaf,Leaf))
    //    prim_new_tyconst ("->", BigInteger.Parse "2")
    //    prim_new_tyconst ("bool", BigInteger.Parse "0")

        let expected = true
        let actual = pretype_ok (Ptycomp ("->", [Ptycomp ("bool", []);Ptycomp ("bool", [])]))

        the_tyconsts.Value <- (dltree_empty : dltree<string,BigInteger>)

        actual
        |> should equal expected

    (* check_pretype tests *)

    [<Fact>]
    let ``check_pretype_test``() =

        the_tyconsts.Value <- Node (1,("->",BigInteger.Parse "2"),Leaf,Node (1,("bool",BigInteger.Parse "0"),Leaf,Leaf))

        let expected = (Ptycomp ("->", [Ptycomp ("bool", []);Ptycomp ("bool", [])]))
        let actual = check_pretype (Ptycomp ("->", [Ptycomp ("bool", []);Ptycomp ("bool", [])]))

        the_tyconsts.Value <- (dltree_empty : dltree<string,BigInteger>)

        actual
        |> should equal expected

    (* new_pretype_gvar tests *)

    [<Fact>]
    let ``new_pretype_gvar_test``() =

        let expected = Ptygvar 0
        let actual = new_pretype_gvar ()

        reset_pretype_gvar_counter () |> ignore

        actual
        |> should equal expected

    (* generate_var_preterm tests *)

    [<Fact>]
    let ``generate_var_preterm_test``() =

        let expected = Ptmvar ("x",Ptygvar 0)
        let actual = generate_var_preterm "x"

        reset_pretype_gvar_counter () |> ignore

        actual
        |> should equal expected

    (* generate_const_preterm tests *)

    [<Fact>]
    let ``generate_const_preterm_test``() =

        the_consts.Value <- Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

        let expected = Ptmconst ("+", Ptycomp ("->", [Ptycomp ("->", [Ptygvar 0; Ptygvar 0]); Ptygvar 0]))
        let actual = generate_const_preterm "+"

        reset_pretype_gvar_counter () |> ignore

        the_consts.Value <- (dltree_empty : dltree<string,hol_type>)

        actual
        |> should equal expected

    (* detype_preterm tests *)

    [<Fact>]
    let ``detype_preterm_test``() =

        the_consts.Value <- Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

        let expected = Ptmconst ("+", Ptycomp ("->", [Ptycomp ("->", [Ptygvar 0; Ptygvar 0]); Ptygvar 0]))
        let actual = detype_preterm (Ptmconst ("+", Ptycomp ("->", [Ptycomp ("->", [Ptyvar "num"; Ptyvar "num"]); Ptyvar "num"])))

        reset_pretype_gvar_counter () |> ignore

        the_consts.Value <- (dltree_empty : dltree<string,hol_type>)

        actual
        |> should equal expected

    (* basic_unify_pretypes tests *)

    [<Fact>]
    let ``basic_unify_pretypes_test``() =

        the_consts.Value <- Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

        let expected = [(Ptygvar 0, Ptyvar "num"); (Ptygvar 0, Ptyvar "num"); (Ptygvar 0, Ptyvar "num")]
        let actual = basic_unify_pretypes 
                        (
                            Ptycomp ("->", [Ptycomp ("->", [Ptyvar "num"; Ptyvar "num"]); Ptyvar "num"]),
                            Ptycomp ("->", [Ptycomp ("->", [Ptygvar 0; Ptygvar 0]); Ptygvar 0])
                        )

        reset_pretype_gvar_counter () |> ignore

        the_consts.Value <- (dltree_empty : dltree<string,hol_type>)

        actual
        |> should equal expected

    (* theta_closure tests *)

    [<Fact>]
    let ``theta_closure_test``() =
        let expected = [(Ptygvar 2, Ptyvar "c"); (Ptygvar 0, Ptyvar "a"); (Ptygvar 1, Ptyvar "b")]
        let actual = theta_closure [(Ptygvar 0, Ptyvar "a"); (Ptygvar 1, Ptyvar "b")] [(Ptygvar 2, Ptyvar "c")]

        actual
        |> should equal expected

    (* unify_pretypes0 tests *)

    [<Fact>]
    let ``unify_pretypes0_already_defined_test``() =
        let expected = [(Ptygvar 0, Ptyvar "a"); (Ptygvar 1, Ptyvar "b"); (Ptygvar 2, Ptyvar "c")]
        let actual = unify_pretypes0 [(Ptygvar 0, Ptyvar "a"); (Ptygvar 1, Ptyvar "b");(Ptygvar 2, Ptyvar "c")] (Ptygvar 2, Ptyvar "c")

        actual
        |> should equal expected

    let ``unify_pretypes0_new_match_test``() =
        let expected = [(Ptygvar 2, Ptyvar "c")]
        let actual = unify_pretypes0 [] (Ptygvar 2, Ptyvar "c")

        actual
        |> should equal expected

    (* unify_pretypes tests *)

    let ``unify_pretypes_test``() =
        let expected = [(Ptygvar 2, Ptyvar "c")]
        let actual = unify_pretypes (Ptygvar 2, Ptyvar "c")

        actual
        |> should equal expected

    (* unify_pretype_list tests *)

    let ``unify_pretype_list_test``() =
        let expected = [(Ptygvar 3, Ptyvar "b"); (Ptygvar 0, Ptyvar "a"); (Ptygvar 2, Ptyvar "c")]
        let actual = unify_pretype_list [(Ptygvar 0, Ptyvar "a"); (Ptygvar 2, Ptyvar "c")] [Ptygvar 3;Ptyvar "b";]

        actual
        |> should equal expected

    (* unify_pretype_pairs tests *)

    let ``unify_pretype_pairs_test``() =
        let expected = [(Ptygvar 4,Ptyvar "d"); (Ptygvar 3, Ptyvar "b"); (Ptygvar 0, Ptyvar "a"); (Ptygvar 2, Ptyvar "c")]
        let actual = unify_pretype_pairs [(Ptygvar 0, Ptyvar "a"); (Ptygvar 2, Ptyvar "c")] [(Ptygvar 3,Ptyvar "b");(Ptygvar 4,Ptyvar "d")]

        actual
        |> should equal expected

    (* varenv_inst tests *)

    let ``varenv_inst_test``() =
        let expected = [("x",[Ptyvar "b"])]
        let actual = varenv_inst [(Ptygvar 0, Ptyvar "a"); (Ptygvar 3, Ptyvar "b")] [("x",[Ptygvar 3;Ptyvar "b"])]

        actual
        |> should equal expected

    (* varenv_subtract tests *)

    let ``varenv_subtract_test``() =
        let expected = [("w",[Ptyvar "c"])]
        let actual = varenv_subtract [("x",[Ptyvar "b"]);("w",[Ptyvar "c"])] ("x",Ptyvar "b")

        actual
        |> should equal expected

    (* varenv_union tests *)

    let ``varenv_union_test``() =
        let expected = [("x",[Ptyvar "b"]);("w",[Ptyvar "c"]);("z",[Ptyvar "a"])]
        let actual = varenv_union [("x",[Ptyvar "b"]);("w",[Ptyvar "c"])] [("z",[Ptyvar "a"])]

        actual
        |> should equal expected

    (* close_name tests *)

    let ``close_name_test``() =
        let (expected:(pretype * pretype) list * varenv) = ([(Ptygvar 4, Ptyvar "b")], [])
        let actual = close_name ("x",Ptyvar "b") ([(Ptygvar 4,Ptyvar "b")],[("x",[Ptyvar "b"])])

        actual
        |> should equal expected

    (* close_all_names tests *)

    let ``close_all_names_test``() =
        let expected = [(Ptygvar 4, Ptyvar "b")]
        let actual = close_all_names ([(Ptygvar 4,Ptyvar "b")],[("x",[Ptyvar "b"])])

        actual
        |> should equal expected

    (* infer_pretypes tests *)

    let ``infer_pretypes_test``() =
        let expected = [(Ptygvar 0, Ptyvar "num")]
        let actual = infer_pretypes 
                            (
                                Ptmcomb (
                                    Ptmcomb (
                                        Ptmconst ("=", Ptycomp ("->", [Ptyvar "num";Ptycomp ("->", [Ptyvar "num";Ptycomp ("bool", [])])])), 
                                        Ptmconst ("1", Ptyvar "num")
                                    ), 
                                    Ptmconst ("1", Ptygvar 0)
                                )
                            )

        actual
        |> should equal expected

    (* resolve_preterm tests *)

    let ``resolve_preterm_test``() =
        let expected = Ptmcomb (
                            Ptmcomb (
                                Ptmconst ("=", Ptycomp ("->", [Ptyvar "num";Ptycomp ("->", [Ptyvar "num";Ptycomp ("bool", [])])])), 
                                Ptmconst ("1", Ptyvar "num")
                            ), 
                            Ptmconst ("1", Ptyvar "num")
                        )

        let actual = resolve_preterm 
                            (
                                Ptmcomb (
                                    Ptmcomb (
                                        Ptmconst ("=", Ptycomp ("->", [Ptyvar "num";Ptycomp ("->", [Ptyvar "num";Ptycomp ("bool", [])])])), 
                                        Ptmconst ("1", Ptyvar "num")
                                    ), 
                                    Ptmconst ("1", Ptygvar 0)
                                )
                            )

        actual
        |> should equal expected
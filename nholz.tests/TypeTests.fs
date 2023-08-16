namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System
open System.Numerics

module TypeFixtures = 
    type TypeFixturesFixture() =
        do 
            ()
        interface IDisposable with

            member __.Dispose () =
                the_tyconsts.Value <- dltree_empty
                ()

module TypeTests = 
    type TypeTests() =
        interface IClassFixture<TypeFixtures.TypeFixturesFixture>

        (* prim_get_tyconst_arity tests *)

        [<Fact>]
        member __.``prim_get_tyconst_arity_test``() =

            the_tyconsts.Value <- Node (1,("A",BigInteger.Parse "1"),Leaf,Node (1,("B",BigInteger.Parse "3"),Leaf,Leaf))
            let actual = prim_get_tyconst_arity "B"

            the_tyconsts.Value <- Leaf

            actual
            |> should equal (BigInteger.Parse "3")

        (* prim_get_all_tyconsts tests *)

        [<Fact>]
        member __.``prim_get_all_tyconsts_test``() =

            the_tyconsts.Value <- Node (1,("A",BigInteger.Parse "1"),Leaf,Node (1,("B",BigInteger.Parse "3"),Leaf,Leaf))
            let actual = prim_get_all_tyconsts()

            the_tyconsts.Value <- Leaf

            actual
            |> should equal [("A",BigInteger.Parse "1");("B",BigInteger.Parse "3")]

        (* is_tyconst_name tests *)

        [<Fact>]
        member __.``is_tyconst_name_test``() =

            the_tyconsts.Value <- Node (1,("A",BigInteger.Parse "1"),Node (1,("B",BigInteger.Parse "0"),Leaf,Leaf),Node (1,("C",BigInteger.Parse "3"),Leaf,Leaf))
            let actual = is_tyconst_name "C"

            the_tyconsts.Value <- Leaf

            actual
            |> should equal true

        (* prim_new_tyconst tests *)

        [<Fact>]
        member __.``prim_new_tyconst_test``() =

            let expected = Node (1,("C",BigInteger.Parse "3"),Leaf,Leaf)
            prim_new_tyconst("C",BigInteger.Parse "3") |> ignore

            let actual = the_tyconsts.Value

            the_tyconsts.Value <- Leaf

            actual
            |> should equal expected

        (* mk_var_type tests *)

        [<Fact>]
        member __.``mk_var_type_test``() =

            mk_var_type "A"
            |> should equal (Tyvar "A")

        (* dest_var_type tests *)

        [<Fact>]
        member __.``dest_var_typee_test``() =

            dest_var_type (Tyvar "A")
            |> should equal "A"

        (* is_var_type tests *)

        [<Fact>]
        member __.``is_var_type_test``() =

            is_var_type (Tyvar "A")
            |> should equal true

        (* mk_comp_type tests *)

        [<Fact>]
        member __.``mk_comp_type_test``() =

            the_tyconsts.Value <- Node (1,("C",BigInteger.Parse "2"),Leaf,Leaf)

            let expected = Tycomp ("C",[Tyvar "A"; Tyvar "C"])
            let actual = mk_comp_type("C",[Tyvar "A"; Tyvar "C"])

            the_tyconsts.Value <- Leaf

            actual
            |> should equal expected

        (* dest_comp_type tests *)

        [<Fact>]
        member __.``dest_comp_type_test``() =

            dest_comp_type (Tycomp ("C",[Tyvar "A"; Tyvar "C"]))
            |> should equal ("C",[Tyvar "A"; Tyvar "C"])

        (* dest_comp_type tests *)

        [<Fact>]
        member __.``is_comp_type_test``() =

            is_comp_type (Tycomp ("C",[Tyvar "A"; Tyvar "C"]))
            |> should equal true

        (* type_eq tests *)

        [<Fact>]
        member __.``type_eq_test``() =

            type_eq (Tycomp ("B",[Tyvar "A"; Tyvar "C"])) (Tycomp ("B",[Tyvar "A"; Tyvar "C"]))
            |> should equal true

        (* type_lt tests *)

        [<Fact>]
        member __.``type_lt_true_test``() =

            type_lt (Tycomp ("B",[Tyvar "A"; Tyvar "C"])) (Tycomp ("B",[Tyvar "A"; Tyvar "D"]))
            |> should equal true

        [<Fact>]
        member __.``type_lt_false1_test``() =

            type_lt (Tycomp ("B",[Tyvar "A"; Tyvar "C"])) (Tycomp ("B",[Tyvar "A"; Tyvar "C"]))
            |> should equal false

        [<Fact>]
        member __.``type_lt_false2_test``() =

            type_lt (Tycomp ("B",[Tyvar "A"; Tyvar "C"])) (Tycomp ("B",[Tyvar "A"; Tyvar "A"]))
            |> should equal false

        (* mk_fun_type tests *)

        [<Fact>]
        member __.``mk_fun_type_test``() =

            mk_fun_type (Tyvar "A", Tyvar "C")
            |> should equal (Tycomp ("->",[Tyvar "A";Tyvar "C"]))

        (* dest_fun_type tests *)

        [<Fact>]
        member __.``dest_fun_type_test``() =

            dest_fun_type (Tycomp ("->",[Tyvar "A";Tyvar "C"]))
            |> should equal (Tyvar "A", Tyvar "C")

        (* is_fun_type tests *)

        [<Fact>]
        member __.``is_fun_type_true_test``() =

            is_fun_type (Tycomp ("->",[Tyvar "A";Tyvar "C"]))
            |> should equal true

        [<Fact>]
        member __.``is_fun_type_false_test``() =

            is_fun_type (Tyvar "A")
            |> should equal false

        (* type_inst tests *)

        [<Fact>]
        member __.``type_inst_test``() =

            the_tyconsts.Value <- Node (1,("->",BigInteger.Parse "2"),Leaf,Leaf)

            let expected = (Tycomp ("->",[Tyvar "C";Tyvar "B"]))
            let actual = type_inst [(Tyvar "A",Tyvar "C")] (Tycomp ("->",[Tyvar "A";Tyvar "B"]))

            the_tyconsts.Value <- Leaf

            actual
            |> should equal expected
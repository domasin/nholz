namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System
open System.Numerics

module TermFixtures = 
    type TermFixturesFixture() =
        do 
            ()
        interface IDisposable with

            member __.Dispose () =
                the_consts.Value <- dltree_empty
                ()

module TermTests = 
    type TermTests() =
        interface IClassFixture<TermFixtures.TermFixturesFixture>

        [<Fact>]
        member __.``get_const_gtype_test``() =

            the_consts.Value <- Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

            let expected = Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])
            let actual = get_const_gtype "+"

            the_consts.Value <- Leaf

            actual
            |> should equal expected

        (* get_all_consts tests *)

        [<Fact>]
        member __.``get_all_consts_test``() =

            the_consts.Value <- Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

            let expected = [("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"]))]
            let actual = get_all_consts()

            the_consts.Value <- Leaf

            actual
            |> should equal expected

        // (* is_const_name tests *)

        // // [<Fact>]
        // member __.``is_const_name_test``() =

        //     the_consts.Value <- Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

        //     let expected = true
        //     let actual = is_const_name "+"

        //     actual
        //     |> should equal expected

        // (* prim_new_const tests *)

        // // [<Fact>]
        // member __.``prim_new_const_test``() =

        //     prim_new_const("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])) |> ignore

        //     let expected = Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)
        //     let actual = !the_consts

        //     actual
        //     |> should equal expected

        // (* term_eq tests *)

        // // [<Fact>]
        // member __.``term_eq_test``() =

        //     term_eq (Tmconst ("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"]))) 
        //         (Tmconst ("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])))
        //     |> should equal true

        // (* term_lt tests *)

        // // [<Fact>]
        // member __.``term_lt_true_test``() =

        //     term_lt (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "C"]))) 
        //         (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "D"])))
        //     |> should equal true

        // // [<Fact>]
        // member __.``term_lt_false1_test``() =

        //     term_lt (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "C"]))) 
        //         (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "C"])))
        //     |> should equal false

        // // [<Fact>]
        // member __.``term_lt_false2_test``() =

        //     term_lt (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "C"]))) 
        //         (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "A"])))
        //     |> should equal false

        // (* type_of tests *)

        // // [<Fact>]
        // member __.``type_of variable/constant test``() =

        //     type_of (Tmconst ("+", Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])))
        //     |> should equal (Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"]))

        // // [<Fact>]
        // member __.``type_of function application test``() =

        //     let func1 = Tmconst ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"]))
        //     let func2 = Tmconst ("1", Tyvar "num")
        //     let funcApp = Tmcomb (func1, func2)

        //     type_of funcApp
        //     |> should equal (Tyvar "string")

        // // [<Fact>]
        // member __.``type_of lambda abstraction test``() =

        //     let var = Tmvar ("x", Tyvar "num")
        //     let trm = Tmconst ("1", Tyvar "num")
        //     let lambdaAbstr = Tmabs (var, trm)

        //     type_of lambdaAbstr
        //     |> should equal (Tycomp ("->",[Tyvar "num";Tyvar "num"]))

        // (* mk_gconst tests *)

        // // [<Fact>]
        // member __.``mk_gconst_test``() =

        //     the_consts.Value <- Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

        //     let expected = Tmconst ("+", Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"]))
        //     let actual = mk_gconst "+"

        //     actual
        //     |> should equal expected

        // (* mk_iconst tests *)

        // // [<Fact>]
        // member __.``mk_iconst_test``() =

        //     the_tyconsts.Value <- Node (1,("->",BigInteger.Parse "2"),Leaf,Leaf)
        //     the_consts.Value <- Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

        //     let expected = Tmconst ("+", Tycomp ("->",[Tycomp ("->",[Tyvar "bool";Tyvar "bool"]);Tyvar "bool"]))
        //     let actual = mk_iconst ("+", [(Tyvar "num",Tyvar "bool")])

        //     actual
        //     |> should equal expected

        // (* mk_comb tests *)

        // // [<Fact>]
        // member __.``mk_comb test``() =

        //     let func1 = Tmconst ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"]))
        //     let func2 = Tmconst ("1", Tyvar "num")
        //     let funcApp = Tmcomb (func1, func2)

        //     mk_comb (func1,func2)
        //     |> should equal funcApp

        // (* dest_comb tests *)

        // // [<Fact>]
        // member __.``dest_comb test``() =

        //     let func1 = Tmconst ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"]))
        //     let func2 = Tmconst ("1", Tyvar "num")
        //     let funcApp = Tmcomb (func1, func2)

        //     dest_comb funcApp
        //     |> should equal (func1,func2)

        // (* is_comb tests *)

        // // [<Fact>]
        // member __.``is_comb true test``() =

        //     let func1 = Tmconst ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"]))
        //     let func2 = Tmconst ("1", Tyvar "num")
        //     let funcApp = Tmcomb (func1, func2)

        //     is_comb funcApp
        //     |> should equal true

        // // [<Fact>]
        // member __.``is_comb false test``() =

        //     let func1 = Tmconst ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"]))
        //     let func2 = Tmconst ("1", Tyvar "num")
        //     let funcApp = Tmcomb (func1, func2)

        //     is_comb func1
        //     |> should equal false

        // (* mk_abs tests *)

        // // [<Fact>]
        // member __.``mk_abs test``() =

        //     let var = Tmvar ("x", Tyvar "num")
        //     let trm = Tmconst ("1", Tyvar "num")
        //     let lambdaAbstr = Tmabs (var, trm)

        //     mk_abs (var,trm)
        //     |> should equal lambdaAbstr
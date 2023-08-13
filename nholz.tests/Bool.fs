namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System

module Fixtures = 
    type BoolFixture() =
        do 
            CoreThry.load |> ignore
            Equal.load |> ignore
            Bool.load |> ignore
        interface IDisposable with

            member __.Dispose () =
                //CLEAN UP TEST DATA OR WHATEVER YOU NEED TO CLEANUP YOUR TESTS
                ()

module BoolTests =
    type BoolTests() =

        [<Fact>]
        member __.``is_bool_eqthm truth_thm returns true`` () =
            is_bool_eqthm truth_thm
            |> should equal false

        [<Fact>]
        member __.``is_bool_eqthm not_true_thm returns true`` () =
            is_bool_eqthm not_true_thm
            |> should equal true

        [<Fact>]
        member __.``"~t" |> parse_term |> is_not returns true`` () =
            "~t" |> parse_term |> is_not
            |> should equal true

        [<Fact>]
        member __.``"~t" |> parse_term |> dest_not |> print_term returns "t"`` () =
            "~t" |> parse_term |> dest_not |> print_term
            |> should equal "t:bool"

        interface IClassFixture<Fixtures.BoolFixture>
namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System

module TheoremFixtures = 

    type TheoremFixture() =
        do 
            CoreThry.load    |> ignore
            Equal.load       |> ignore
            Bool.load        |> ignore
            BoolAlg.load     |> ignore
            BoolClass.load   |> ignore
            Pair.load        |> ignore
            Ind.load         |> ignore
            Nat.load         |> ignore
            NatNumrl.load    |> ignore
            NatArith.load    |> ignore
            NatRel.load      |> ignore
            NatEval.load     |> ignore
        interface IDisposable with

            member __.Dispose () =
                //CLEAN UP TEST DATA OR WHATEVER YOU NEED TO CLEANUP YOUR TESTS
                ()


module BoolTests =
    type BoolTests() =
        interface IClassFixture<TheoremFixtures.TheoremFixture>

        [<Fact>]
        member __.``Central Test: |- 2 - 1 = 1 shuold be proved`` () =

            // since eval_sub_conv is the last "theorem" scheme if this test succeeds everything's ok

            let expected = "2 - 1 = 1" |> parse_term

            "2 - 1"
            |> parse_term
            |> eval_sub_conv
            |> concl
            |> should equal expected
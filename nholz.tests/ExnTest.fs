namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System

module ExnTests =

    [<Fact>]
    let ``should fail with HolFail and message``() = 
        let func xs = 
            match xs with
            | [] -> hol_fail ("func","Empty list")
            | _ -> 1 + 2

        (fun () -> func [] |> ignore) 
        |> should (throwWithMessage "[HZ] FAIL: func - Empty list") typeof<HolFail>
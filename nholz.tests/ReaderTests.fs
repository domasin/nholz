namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System

module ReaderTests = 

    [<Fact>]
    let ``ReformulateRHS_test``() =

        let lhdFunc x = "pippo " + x
        let readerFn x = ("pippo", x)

        (lhdFunc @| readerFn) "prova"
        |> should equal ("pippo pippo", "prova")

    [<Fact>]
    let ``Exception if RHS succeeds test``() =

        let lhdFunc x = "pippo " + x
        let readerFn x = ("pippo", x)

        (lhdFunc @!| readerFn) "prova"
        |> should equal "pippo pippo"

    [<Fact>]
    let ``Alternation test``() =

        let read_fn1 x = 
            match x with
            | "pippo" -> raise ReadFail
            | _ -> x

        let readerFn2 x = "pippo " + x

        (!|||) read_fn1  readerFn2 "pippo"
        |> should equal "pippo pippo"

    //    (read_fn1 (!|||) readerFn2) "pippo"
    //    |> should equal "pippo pippo"

    [<Fact>]
    let ``Serial !>>> test``() =

        let read_fn1 (x:string) = 
            let x1 = x.Substring(0,2)
            let x2 = x.Replace(x1,"")
            x1,x2

        let read_fn2 (x:string) = 
            let x1 = x.Substring(0,2)
            let x2 = x.Replace(x1,"")
            x1,x2

        (!>>>) read_fn1 read_fn2 "pippo"
        |> should equal (("pi", "pp"), "o")
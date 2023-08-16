namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System
open System.Numerics

module Fixtures = 
    type ParserTestsFixture() =
        do 
            the_tyconsts.Value <-  
              Node
                (2,("->", BigInteger.Parse "2"),Node (1,("#", BigInteger.Parse    "2"),Leaf,Leaf),
                 Node
                   (2,("ind", BigInteger.Parse "0"),Node (1,("bool",   BigInteger.Parse "0"),Leaf,Leaf),
                    Node (1,("nat", BigInteger.Parse "0"),Leaf,Leaf)))

            the_type_fixities.Value <-  
              Node
                (1,("#", Infix (10, RightAssoc)),Leaf,
                 Node (1,("->", Infix (5, RightAssoc)),Leaf,Leaf))

            the_fixities.Value <-  
              Node
                (4,("==>", Infix (10, RightAssoc)),
                 Node
                   (3,(@"/\", Infix (20, RightAssoc)),
                    Node
                      (2,("+", Infix (50, LeftAssoc)),
                       Node
                         (1,("!", Binder),Leaf,
                          Node (1,("*", Infix (55, LeftAssoc)),Leaf,Leaf)),
                       Node (1,("-", Infix (50, LeftAssoc)),Leaf,Leaf)),
                    Node
                      (2,("<=>", Infix (5, NonAssoc)),
                       Node
                         (1,("<", Infix (40, NonAssoc)),Leaf,
                          Node (1,("<=", Infix (40, NonAssoc)),Leaf,Leaf)),
                       Node (1,("=", Infix (30, NonAssoc)),Leaf,Leaf))),
                 Node
                   (3,("@", Binder),
                    Node
                      (2,("?", Binder),
                       Node
                         (1,(">", Infix (40, NonAssoc)),Leaf,
                          Node (1,(">=", Infix (40, NonAssoc)),Leaf,Leaf)),
                       Node (1,("?!", Binder),Leaf,Leaf)),
                    Node
                      (2,(@"\/", Infix (15, RightAssoc)),
                       Node (1,("EXP", Infix (60, LeftAssoc)),Leaf,Leaf),
                       Node (1,("~", Prefix),Leaf,Leaf))))

            
        interface IDisposable with

            member __.Dispose () =
                the_tyconsts.Value <- dltree_empty
                the_type_fixities.Value <- dltree_empty
                the_fixities.Value <- dltree_empty
                ()

module ParserTests = 
    type ParserTests() =
        interface IClassFixture<Fixtures.ParserTestsFixture>

        [<Fact>]
        member __.``parse_type_test``() =
            let expected = Tycomp ("->", [Tycomp ("bool", []); Tycomp ("bool", [])])

            let test() = 
                printfn "%A" (the_tyconsts) |> ignore
                parse_type("bool->bool")

            test()
            |> should equal expected

        
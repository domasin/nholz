namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System.Numerics

module LexerTests = 

    (* funcPunct tests *)

    [<Fact>]
    let ``funcPunct_test``() =

        lex ['(';')';',']
        |> should equal [Resword_tok "("; Resword_tok ")"; Resword_tok ","]

    (* funcAlphanumeric tests *)

    [<Fact>]
    let ``funcAlphanumeric_test``() =

        lex ['_';'b';'c']
        |> should equal [Ident_tok (false, No_mark, "_bc")]

    (* funcNumeric tests *)

    [<Fact>]
    let ``funcNumeric_test``() =

        lex ['1';'2';'3']
        |> should equal [Numeric_tok (false, No_mark, "123")]

    (* funcSymbolic tests *)

    [<Fact>]
    let ``funcSymbolic_test``() =

        lex ['!';'#';'&';'*';'+';'-';'.';'/';';';'<';'=';'>';'?';'@';'[';'\\';']';'^';'{';';';'}';'~']
        |> should equal [Ident_tok (false, No_mark, "!#&*+-./;<=>?@[\\]^{;}~")]
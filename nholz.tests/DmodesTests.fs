namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System.Numerics

module DmodesTests = 

    (* set_type_annotation_mode tests *)

    [<Fact>]
    let ``set_type_annotation_mode_test``() =

        set_type_annotation_mode Full |> ignore
        let expected = Full
        let actual = the_type_annotation_mode.Value

        the_type_annotation_mode.Value <- Minimal

        actual
        |> should equal expected

    (* get_type_annotation_mode tests *)

    [<Fact>]
    let ``get_type_annotation_mode_test``() =

        let expected = Minimal
        let actual = get_type_annotation_mode ()

        actual
        |> should equal expected

    (* set_tyvar_marking_mode tests *)

    [<Fact>]
    let ``set_tyvar_marking_mode_test``() =

        set_tyvar_marking_mode Minimal |> ignore
        let expected = Minimal
        let actual = the_tyvar_marking_mode.Value

        the_tyvar_marking_mode.Value <- Full

        actual
        |> should equal expected

    (* get_tyvar_marking_mode tests *)

    [<Fact>]
    let ``get_tyvar_marking_mode_test``() =

        let expected = Full
        let actual = get_tyvar_marking_mode ()

        actual
        |> should equal expected

    (* set_var_marking_mode tests *)

    [<Fact>]
    let ``set_var_marking_mode_test``() =

        set_var_marking_mode Full |> ignore
        let expected = Full
        let actual = the_var_marking_mode.Value

        the_var_marking_mode.Value <- Minimal

        actual
        |> should equal expected

    (* get_var_marking_mode tests *)

    [<Fact>]
    let ``get_var_marking_mode_test``() =

        let expected = Minimal
        let actual = get_var_marking_mode ()

        actual
        |> should equal expected

    (* set_language_level_mode tests *)

    [<Fact>]
    let ``set_language_level_mode_test``() =

        set_language_level_mode Minimal |> ignore
        let expected = Minimal
        let actual = the_language_level_mode.Value

        the_language_level_mode.Value <- Full

        actual
        |> should equal expected

    (* get_language_level_mode tests *)

    [<Fact>]
    let ``get_language_level_mode_test``() =

        let expected = Full
        let actual = get_language_level_mode ()

        actual
        |> should equal expected
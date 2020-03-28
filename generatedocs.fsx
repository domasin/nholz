// Given a typical setup (with 'FSharp.Formatting' referenced using NuGet),
// the following will include binaries and load the literate script
#load "packages/FSharp.Formatting.3.1.0/FSharp.Formatting.fsx"
open System.IO
open FSharp.Literate
open FSharp.Formatting.Razor

/// Return path relative to the current file location
let relative subdir = Path.Combine(__SOURCE_DIRECTORY__, subdir)

/// Processes a single F# Script file and produce HTML output
let processScriptAsHtml (docfile) =
  let file = Path.Combine(__SOURCE_DIRECTORY__, "manuale\\teoremi\\" + docfile + ".fsx")
  let output = relative ("docs/" + docfile + ".html")
  let template = relative "manuale/template-file.html"
  RazorLiterate.ProcessScriptFile(file, template, output, lineNumbers=false)

processScriptAsHtml (@"0004_bool_cases")

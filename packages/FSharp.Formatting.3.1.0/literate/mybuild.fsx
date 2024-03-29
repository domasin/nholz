﻿// Given a typical setup (with 'FSharp.Formatting' referenced using NuGet),
// the following will include binaries and load the literate script
#load "../FSharp.Formatting.fsx"
open System.IO
open FSharp.Literate
open FSharp.Formatting.Razor

// ----------------------------------------------------------------------------
// SETUP
// ----------------------------------------------------------------------------

/// Return path relative to the current file location
let relative subdir = Path.Combine(__SOURCE_DIRECTORY__, subdir)

// Create output directories & copy content files there
// (We have two sets of samples in "output" and "output-all" directories,
//  for simplicitly, this just creates them & copies content there)
if not (Directory.Exists(relative "output")) then
  Directory.CreateDirectory(relative "output") |> ignore
  Directory.CreateDirectory (relative "output/content") |> ignore

for fileInfo in DirectoryInfo(relative "../../docs/files/content").EnumerateFiles() do
  fileInfo.CopyTo(Path.Combine(relative "output/content", fileInfo.Name)) |> ignore

// ----------------------------------------------------------------------------
// EXAMPLES
// ----------------------------------------------------------------------------

/// Processes a single F# Script file and produce HTML output
let processScriptAsHtml () =
  let file = @"C:\Users\masinido\source\repos\nholz\manuale\A5_Inference_Rules.fsx"
  let output = relative "output/A5_Inference_Rules.html"
  let template = relative "templates/template-file.html"
  RazorLiterate.ProcessScriptFile(file, template, output)

/// Processes a single F# Script file and produce LaTeX output
let processScriptAsLatex () =
  let file = relative "demo.fsx"
  let output = relative "output/demo-script.tex"
  let template = relative "templates/template-color.tex"
  RazorLiterate.ProcessScriptFile(file, template, output, format = OutputKind.Latex)

/// Processes a single Markdown document and produce HTML output
let processDocAsHtml () =
  let file = relative "demo.md"
  let output = relative "output/demo-doc.html"
  let template = relative "templates/template-file.html"
  RazorLiterate.ProcessMarkdown(file, template, output)

/// Processes a single Markdown document and produce LaTeX output
let processDocAsLatex () =
  let file = relative "demo.md"
  let output = relative "output/demo-doc.tex"
  let template = relative "templates/template-color.tex"
  RazorLiterate.ProcessMarkdown(file, template, output, format = OutputKind.Latex)


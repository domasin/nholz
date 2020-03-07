Literate sample
===============

This file demonstrates how to write Markdown document with 
embedded F# snippets that can be transformed into nice HTML 
using the `literate.fsx` script from the [F# Formatting
package](http://fsprojects.github.io/FSharp.Formatting).

In this case, the document itself is a valid Markdown and 
you can use standard Markdown features to format the text:

 - Here is an example of unordered list and...
 - Text formatting including **bold** and _emphasis_

For more information, see the [Markdown][md] reference.

 [md]: http://daringfireball.net/projects/markdown


Writing F# code
---------------
In standard Markdown, you can include code snippets by 
writing a block indented by four spaces and the code 
snippet will be turned into a `<pre>` element. If you do 
the same using Literate F# tool, the code is turned into
a nicely formatted F# snippet:

    let ramsey s t n =
        let vertices = 1 -- n in
        let yesgrps = map (allsets 2) (allsets s vertices)
        and nogrps = map (allsets 2) (allsets t vertices) in
        let e[m;n] = Atom(P("p_"^(string_of_int m)^"_"^(string_of_int n))) in
        Or(list_disj (map (list_conj ** map e) yesgrps),
            list_disj (map (list_conj ** map (fun p -> Not(e p))) nogrps));;


Hiding code
-----------

If you want to include some code in the source code, 
but omit it from the output, you can use the `hide` 
command. You can also use `module=...` to specify that 
the snippet should be placed in a separate module 
(e.g. to avoid duplicate definitions).

    [hide, module=Hidden]
    /// This is a hidden answer
    let answer = 42

The value will be deffined in the F# code that is 
processed and so you can use it from other (visible) 
code and get correct tool tips:

    let answer = Hidden.answer


Including other snippets
------------------------

When writing literate programs as Markdown documents, 
you can also include snippets in other languages. 
These will not be colorized and processed as F# 
code samples:

    [lang=csharp]
    Console.WriteLine("Hello world!");

This snippet is turned into a `pre` element with the
`lang` attribute set to `csharp`.
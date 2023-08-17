#r "nuget: nholz2"
open HOL

let latexStr (loc:Proof Location) =
    let (Loc(Tree((exp,_,_),_), _)) = loc
    let proof = loc |> root
    proof 
    |> treeToLatex 1 exp
    |> fun x -> x.Replace("\\color{green}", "")
    |> fun x -> x.Replace("\\textsf", "")
    |> fun x -> x.Replace("_", "\\_")

module HolTypeAndTermsFormatter =
    Formatter.SetPreferredMimeTypesFor(typeof<hol_type> ,"text/html")
    Formatter.Register<hol_type>((fun ty -> print_type ty), "text/html")

    Formatter.SetPreferredMimeTypesFor(typeof<term> ,"text/html")
    Formatter.Register<term>((fun tm -> print_term tm), "text/html")
    Formatter.Register<term list>((fun xs -> 
                                    xs
                                    |> Seq.map (print_term)
                                    |> fun x -> sprintf "[%s]" (x |> String.concat ", ")),"text/html")
    Formatter.Register<term * term>((fun (x,y) -> 
        sprintf "(%s, %s)" (x |> print_term) (y |> print_term)
    ),"text/html")

    Formatter.SetPreferredMimeTypesFor(typeof<thm> ,"text/html")
    Formatter.Register<thm>((fun thm -> print_thm thm), "text/html")

    Formatter.SetPreferredMimeTypesFor(typeof<Proof Location> ,"text/html")
    Formatter.Register<Proof Location>((fun loc -> "$" + (latexStr loc) + "$"), "text/html")
    
CoreThry.load
Equal.load
Bool.load
BoolAlg.load
BoolClass.load




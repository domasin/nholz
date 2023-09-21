// ------------------------------------------------------------------------- //
// Printing of fol terms.                                                    //
// ------------------------------------------------------------------------- //

let rec fprint_term tw prec fm =
    match fm with
    | Var x ->
        fprintf tw "%s" x
    | Fn ("^", [tm1; tm2;]) ->
        fprint_infix_term tw true prec 24 "^" tm1 tm2
    | Fn ("/", [tm1; tm2;]) ->
        fprint_infix_term tw true prec 22 "/" tm1 tm2
    | Fn ("*", [tm1; tm2;]) ->
        fprint_infix_term tw false prec 20 "*" tm1 tm2
    | Fn ("-", [tm1; tm2;]) ->
        fprint_infix_term tw true prec 18 "-" tm1 tm2
    | Fn ("+", [tm1; tm2;]) ->
        fprint_infix_term tw false prec 16 "+" tm1 tm2
    | Fn ("::", [tm1; tm2;]) ->
        fprint_infix_term tw false prec 14 "::" tm1 tm2
    | Fn (f, args) ->
        fprint_fargs tw f args

and fprint_fargs tw f args =
    fprintf tw "%s" f
    if args <> [] then
        fprintf tw "("
        fprint_term tw 0 (List.head args)
        List.iter (
                    fun t -> 
                    fprintf tw ","
                    fprint_term tw 0 t)
            (List.tail args)
        fprintf tw ")"

and fprint_infix_term tw isleft oldprec newprec sym p q =
    if oldprec > newprec then 
        fprintf tw "("
    fprint_term tw (if isleft then newprec else newprec + 1) p
    fprintf tw "%2s " sym
    fprint_term tw (if isleft then newprec + 1 else newprec) q
    if oldprec > newprec then
        fprintf tw ")"

let fprintert tw tm =
    // fprintf tw "<<|"
    fprint_term tw 0 tm
    // fprintf tw "|>>"

let inline print_term t = fprintert stdout t
let inline sprint_term t = writeToString (fun sw -> fprintert sw t)

// ------------------------------------------------------------------------- //
// Printing of formulas.                                                     //
// ------------------------------------------------------------------------- //

let fprint_atom tw prec (R (p, args)) : unit =
    if mem p ["="; "<"; "<="; ">"; ">="] && List.length args = 2 then
        fprint_infix_term tw false 12 12 (" " + p) (List.nth args 0) (List.nth args 1)
    else
        fprint_fargs tw p args

let inline print_atom prec arg = fprint_atom stdout prec arg
let inline sprint_atom prec arg = writeToString (fun sw -> fprint_atom sw prec arg)

let fbracket tw p n f x y =
    if p then fprintf tw "("
    f x y
    if p then fprintf tw ")"

let rec strip_quant fm =
    match fm with
    | Forall (x, (Forall (y, p) as yp))
    | Exists (x, (Exists (y, p) as yp)) ->
        let xs, q = strip_quant yp
        (x :: xs), q
    | Forall (x, p)
    | Exists (x, p) ->
        [x], p
    | _ ->
        [], fm

let fprint_formula tw pfn =
    let rec print_formula pr fm =
        match fm with
        | False ->
            fprintf tw "false"
        | True ->
            fprintf tw "true"
        | Atom pargs ->
            pfn pr pargs
        | Not p ->
            fbracket tw (pr > 10) 1 (print_prefix 10) "~" p
        | And (p, q) ->
            fbracket tw (pr > 8) 0 (print_infix 8 "/\\") p q
        | Or (p, q) ->
            fbracket tw (pr > 6) 0 (print_infix  6 "\\/") p q
        | Imp (p, q) ->
            fbracket tw (pr > 4) 0 (print_infix 4 "==>") p q
        | Iff (p, q) ->
            fbracket tw (pr > 2) 0 (print_infix 2 "<=>") p q
        | Forall (x, p) ->
            fbracket tw (pr > 0) 2 print_qnt "forall" (strip_quant fm)
        | Exists (x, p) ->
            fbracket tw (pr > 0) 2 print_qnt "exists" (strip_quant fm)

    and print_qnt qname (bvs, bod) =
        fprintf tw "%s" qname
        List.iter (fprintf tw " %s") bvs
        fprintf tw ". "
        print_formula 0 bod

    and print_prefix newpr sym p =
        fprintf tw "%s" sym
        print_formula (newpr + 1) p

    and print_infix newpr sym p q =
        print_formula (newpr + 1) p
        fprintf tw " %s " sym
        print_formula newpr q

    print_formula 0

let fprint_qformula tw pfn fm =
    fprintf tw "<<"
    fprint_formula tw pfn fm
    fprintf tw ">>"

let fprint_fol_formula tw =
    fprint_qformula tw (fprint_atom tw)
  
let inline print_fol_formula f = fprint_fol_formula stdout f
let inline sprint_fol_formula f = writeToString (fun sw -> fprint_fol_formula sw f)
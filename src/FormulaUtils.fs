// This file contains implementations of the functions described in the book
// "handbook of practical logic and automated reasoning"
// (https://www.cl.cam.ac.uk/~jrh13/atp/) adapted to fit the nholz hol system.
// Many of the implementations are based on the version of the code ported in
// F# by https://github.com/jack-pappas/fsharp-logic-examples/

module HOL.FormulaUtils

// ------------------------------------------------------------------------- //
// Active patterns to make reuse of logic-examles code easier                //
// ------------------------------------------------------------------------- //

let (|False|_|) tm =
    match tm with
    | Tmconst ("false", Tycomp ("bool", [])) -> Some false_tm
    | _ -> None

let (|True|_|) tm =
    match tm with
    | Tmconst ("true", Tycomp ("bool", [])) -> Some true_tm
    | _ -> None

let (|Atom|_|) tm =
    match tm with
    | Tmvar (p, Tycomp ("bool", [])) -> Some p
    | _ -> None

let (|Not|_|) tm =
    match tm with
    | Tmcomb (Tmconst ("~", Tycomp ("->", [ Tycomp ("bool", []); Tycomp ("bool", []) ])), p) -> Some p
    | _ -> None

let (|And|_|) tm =
    match tm with
    | Tmcomb (Tmcomb (Tmconst ("/\\",
                               Tycomp ("->",
                                       [ Tycomp ("bool", [])
                                         Tycomp ("->", [ Tycomp ("bool", []); Tycomp ("bool", []) ]) ])),
                      p),
              q) -> Some(p, q)
    | _ -> None

let (|Or|_|) tm =
    match tm with
    | Tmcomb (Tmcomb (Tmconst ("\\/",
                               Tycomp ("->",
                                       [ Tycomp ("bool", [])
                                         Tycomp ("->", [ Tycomp ("bool", []); Tycomp ("bool", []) ]) ])),
                      p),
              q) -> Some(p, q)
    | _ -> None

let (|Imp|_|) tm =
    match tm with
    | Tmcomb (Tmcomb (Tmconst ("==>",
                               Tycomp ("->",
                                       [ Tycomp ("bool", [])
                                         Tycomp ("->", [ Tycomp ("bool", []); Tycomp ("bool", []) ]) ])),
                      p),
              q) -> Some(p, q)
    | _ -> None

let (|Iff|_|) tm =
    match tm with
    | Tmcomb (Tmcomb (Tmconst ("=",
                               Tycomp ("->",
                                       [ Tycomp ("bool", [])
                                         Tycomp ("->", [ Tycomp ("bool", []); Tycomp ("bool", []) ]) ])),
                      p),
              q) -> Some(p, q)
    | _ -> None

let (|Forall|_|) tm =
    match tm |> is_forall with
    | true -> Some(tm |> dest_forall)
    | _ -> None

let (|Exists|_|) tm =
    match tm |> is_exists with
    | true -> Some(tm |> dest_exists)
    | _ -> None

// ------------------------------------------------------------------------- //
// Apply a function to the atoms, otherwise keeping structure.               //
// ------------------------------------------------------------------------- //

let rec onatoms f fm =
   match fm with
   | Atom a -> f a
   | Not p -> mk_not (onatoms f p)
   | And (p, q) -> mk_conj (onatoms f p, onatoms f q)
   | Or (p, q) -> mk_disj (onatoms f p, onatoms f q)
   | Imp (p, q) -> mk_imp (onatoms f p, onatoms f q)
   | Iff (p, q) -> mk_eq (onatoms f p, onatoms f q)
   | Forall (x, p) -> mk_forall (x, onatoms f p)
   | Exists (x, p) -> mk_exists (x, onatoms f p)
   | _ -> fm

// ------------------------------------------------------------------------- //
// Formula analog of list iterator "List.foldBack".                          //
// ------------------------------------------------------------------------- //

/// the term is a boolean atom
let is_bool_atom tm = 
    tm |> is_bool_term && (tm |> is_const || tm |> is_var)

let rec overatoms f tm b =
   match tm with
   | Atom _ -> 
      f tm b
   | Not p -> 
      overatoms f p b
   | And (p,q) 
   | Or (p, q)
   | Imp (p, q)
   | Iff (p, q)
      -> overatoms f p (overatoms f q b)
    | Forall (x, p)
    | Exists (x, p) ->
        overatoms f p b
    | _ -> b

// ------------------------------------------------------------------------- //
// Special case of a union of the results of a function over the atoms.      //
// ------------------------------------------------------------------------- //

let atom_union f tm =
    (tm, [])
    ||> overatoms (fun h (t) -> (f h) @ t)
    |> setify
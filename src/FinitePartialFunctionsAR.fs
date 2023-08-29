/// Functions to automate tautology and satisfiability in the propositional 
/// fragment.
/// 
/// The module implements ideas described in the book "handbook of practical
/// logic and automated reasoning" (https://www.cl.cam.ac.uk/~jrh13/atp/)
/// adapting the code to fit nholz HOL system.
/// 
/// Many of the implementations are based on the version of the code ported in 
/// F# by https://github.com/jack-pappas/fsharp-logic-examples/.

/// Polymorphic finite partial functions via Patricia trees. 
[<AutoOpen>]
module HOL.AutomatedReasoning.FPF

open HOL

// ------------------------------------------------------------------------- //
// Polymorphic finite partial functions via Patricia trees.                  //
//                                                                           //
// The point of this strange representation is that it is canonical (equal   //
// functions have the same encoding) yet reasonably efficient on average.    //
//                                                                           //
// Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        //
// ------------------------------------------------------------------------- //
//

type func<'a,'b> =
    | Empty
    | Leaf of int * ('a * 'b) list
    | Branch of int * int * func<'a,'b> * func<'a,'b>

let rec string_of_patricia_tree_with_level pt (level : int) =
    match pt with
    | Empty  -> 
        let emptyindent = String.replicate level " "        
        emptyindent + "Empty"
    | Leaf (n,l) ->
        let leafindent = String.replicate level " "
        let leaf = "Leaf " + string n 
        let valueindent = String.replicate (level + 1) " "
        let value = sprintf "%A" l
        leafindent + leaf + "\n" + valueindent + value
    | Branch (n1, n2, b1, b2) ->
        let branchindent = String.replicate level " "
        let branchIndex = string n1 + "," + string n2
        let branch1 = string_of_patricia_tree_with_level b1 (level + 1)
        let branch2 = string_of_patricia_tree_with_level b2 (level + 1)
        let branch = "Branch " + branchIndex 
        branchindent + branch  + "\n" + branch1  + "\n" + branch2

let rec string_of_patricia_tree pt =
    string_of_patricia_tree_with_level pt 0

let sprint_patricia_tree pt =
    string_of_patricia_tree pt

let print_patricia_tree pt =
    printfn "%O" (sprint_patricia_tree pt) |> ignore

// ------------------------------------------------------------------------- //
// Undefined function.                                                       //
// ------------------------------------------------------------------------- //

let undefined = Empty

// ------------------------------------------------------------------------- //
// In case of equality comparison worries, better use this.                  //
// ------------------------------------------------------------------------- //

let is_undefined = function
    | Empty -> true
    | _     -> false

// ------------------------------------------------------------------------- //
// Operation analogous to "map" for lists.                                   //
// ------------------------------------------------------------------------- //

let mapf =
    let rec map_list f l =
        match l with
        | [] -> []
        | (x, y) :: t ->
            (x, f y) :: (map_list f t)
    let rec mapf f t =
        match t with
        | Empty -> Empty
        | Leaf (h, l) ->
            Leaf (h, map_list f l)
        | Branch (p, b, l, r) ->
            Branch (p, b, mapf f l, mapf f r)
    mapf

// ------------------------------------------------------------------------- //
// Operations analogous to "fold" for lists.                                 //
// ------------------------------------------------------------------------- //

// Support function for use with graph, dom, and ran.
let foldl =
    let rec foldl_list f a l =
        match l with
        | [] -> a
        | (x, y) :: t ->
            foldl_list f (f a x y) t
    let rec foldl f a t =
        match t with
        | Empty -> a
        | Leaf (h, l) ->
            foldl_list f a l
        | Branch (p, b, l, r) ->
            foldl f (foldl f a l) r
    foldl
        
// Support fucntion for end user use if needed. 
// Not used in handbook code.
let foldr =
    let rec foldr_list f l a =
        match l with
        | [] -> a
        | (x, y) :: t ->
            f x y (foldr_list f t a)
    let rec foldr f t a =
        match t with
        | Empty -> a
        | Leaf (h, l) ->
            foldr_list f l a
        | Branch (p, b, l, r) ->
            foldr f l (foldr f r a)
    foldr

// ------------------------------------------------------------------------- //
// Mapping to sorted-list representation of the graph, domain and range.     //
// ------------------------------------------------------------------------- //

let graph f =
    foldl (fun a x y -> (x, y) :: a) [] f
    |> setify
    
let dom f =
    foldl (fun a x y -> x :: a) [] f
    |> setify
    
let ran f =
    foldl (fun a x y -> y :: a) [] f
    |> setify

// ------------------------------------------------------------------------- //
// Application.                                                              //
// ------------------------------------------------------------------------- //

// Support function for use with apply, tryapplyd, and tryapplyl.
let applyd =
    let rec apply_listd l d x =
        match l with
        | [] -> d x
        | (a, b) :: tl ->
            let c = compare x a
            if c = 0 then b
            elif c > 0 then apply_listd tl d x
            else d x
            
    fun f d x ->
        let k = hash x
        let rec look t =
            match t with
            | Leaf (h, l) when h = k ->
                apply_listd l d x
            | Branch (p, b, l, r) when (k ^^^ p) &&& (b - 1) = 0 ->
                if k &&& b = 0 then l else r
                |> look
            | _ -> d x
        look f

let apply f =
    applyd f (fun _ -> failwith "apply")

let tryapplyd f a d =
    applyd f (fun _ -> d) a

let tryapplyl f x =
    tryapplyd f x []
    
let defined f x =
    try
        apply f x |> ignore
        true
    with
    | Failure _ -> false

// ------------------------------------------------------------------------- //
// Undefinition.                                                             //
// ------------------------------------------------------------------------- //

let undefine =
    let rec undefine_list x l =
        match l with
        | [] -> []
        | (a, b as ab) :: t ->
                let c = compare x a
                if c = 0 then t
                elif c < 0 then l
                else
                    let t' = undefine_list x t
                    if t' = t then l
                    else ab :: t'
                              
    fun x ->
        let k = hash x
        let rec und t =
            match t with
            | Leaf (h, l) when h = k ->
                let l' = undefine_list x l
                if l' = l then t
                elif l' = [] then Empty
                else Leaf (h, l')

            | Branch (p, b, l, r) when k &&& (b - 1) = p ->
                if k &&& b = 0 then
                    let l' = und l
                    if l' = l then t
                    else
                        match l' with
                        | Empty -> r
                        | _ -> Branch (p, b, l', r)
                else
                    let r' = und r
                    if r' = r then t
                    else
                        match r' with
                        | Empty -> l
                        | _ -> Branch (p, b, l, r')
            | _ -> t
        und

// ------------------------------------------------------------------------- //
// Redefinition and combination.                                             //
// ------------------------------------------------------------------------- //

// Finite Partial Functions (FPF)

// To update the FPF with a new mapping from x to y.
// Support function for use with FPF
let (|->),combine =
    let newbranch p1 t1 p2 t2 =
        let zp = p1 ^^^ p2
        let b = zp &&& -zp
        let p = p1 &&& (b - 1)
        if p1 &&& b = 0 then Branch (p, b, t1, t2)
        else Branch (p, b, t2, t1)

    let rec define_list (x, y as xy) l =
        match l with
        | [] -> [xy]
        | (a, b as ab) :: t ->
            let c = compare x a
            if c = 0 then xy :: t
            elif c < 0 then xy :: l
            else ab :: (define_list xy t)

    and combine_list op z l1 l2 =
        match l1, l2 with
        | [], x
        | x, [] -> x
        | ((x1, y1 as xy1) :: t1, (x2, y2 as xy2) :: t2) ->
            let c = compare x1 x2
            if c < 0 then xy1 :: (combine_list op z t1 l2)
            elif c > 0 then xy2 :: (combine_list op z l1 t2)
            else
                let y = op y1 y2
                let l = combine_list op z t1 t2
                if z y then l
                else (x1, y) :: l

    let (|->) x y =
        let k = hash x
        let rec upd t =
            match t with
            | Empty -> Leaf (k, [x, y])
            | Leaf (h, l) ->
                if h = k then Leaf (h, define_list (x, y) l)
                else newbranch h t k (Leaf (k, [x, y]))
            | Branch (p, b, l, r) ->
                if k &&& (b - 1) <> p then newbranch p t k (Leaf (k, [x, y]))
                elif k &&& b = 0 then Branch (p, b, upd l, r)
                else Branch (p, b, l, upd r)
        upd

    let rec combine op z t1 t2 =
        match t1, t2 with
        | Empty, x
        | x, Empty -> x
        | Leaf (h1, l1), Leaf (h2, l2) ->
            if h1 = h2 then
                let l = combine_list op z l1 l2
                if l = [] then Empty
                else Leaf (h1, l)
            else newbranch h1 t1 h2 t2

        | (Leaf (k, lis) as lf), (Branch (p, b, l, r) as br) ->
            if k &&& (b - 1) = p then
                if k &&& b = 0 then
                    match combine op z lf l with
                    | Empty -> r
                    | l' -> Branch (p, b, l', r)
                else
                    match combine op z lf r with
                    | Empty -> l
                    | r' -> Branch (p, b, l, r')
            else
                newbranch k lf p br

        | (Branch (p, b, l, r) as br), (Leaf (k, lis) as lf) ->
            if k &&& (b - 1) = p then
                if k &&& b = 0 then
                    match combine op z l lf with
                    | Empty -> r
                    | l' -> Branch (p, b, l', r)
                else
                    match combine op z r lf with
                    | Empty -> l
                    | r' -> Branch (p, b, l, r')
            else
                newbranch p br k lf

        | Branch (p1, b1, l1, r1), Branch (p2, b2, l2, r2) ->
            if b1 < b2 then
                if p2 &&& (b1 - 1) <> p1 then
                    newbranch p1 t1 p2 t2
                elif p2 &&& b1 = 0 then
                    match combine op z l1 t2 with
                    | Empty -> r1
                    | l -> Branch (p1, b1, l, r1)
                else
                    match combine op z r1 t2 with
                    | Empty -> l1
                    | r -> Branch (p1, b1, l1, r)

            elif b2 < b1 then
                if p1 &&& (b2 - 1) <> p2 then
                    newbranch p1 t1 p2 t2
                elif p1 &&& b2 = 0 then
                    match combine op z t1 l2 with
                    | Empty -> r2
                    | l -> Branch (p2, b2, l, r2)
                else
                    match combine op z t1 r2 with
                    | Empty -> l2
                    | r -> Branch (p2, b2, l2, r)

            elif p1 = p2 then
                match combine op z l1 l2, combine op z r1 r2 with
                | Empty, x
                | x, Empty -> x
                | l, r ->
                    Branch (p1, b1, l, r)
            else
                newbranch p1 t1 p2 t2

    (|->), combine

// ------------------------------------------------------------------------- //
// Special case of point function.                                           //
// ------------------------------------------------------------------------- //

// Finite Partial Functions (FPF)
// To create a new funtion in the FPF defined only for the value x and 
// mapping it to y.
let (|=>) x y = 
    (x |-> y) undefined

// ------------------------------------------------------------------------- //
// Idiom for a mapping zipping domain and range lists.                       //
// ------------------------------------------------------------------------- //

let fpf xs ys =
    List.foldBack2 (|->) xs ys undefined

// ------------------------------------------------------------------------- //
// Grab an arbitrary element.                                                //
// ------------------------------------------------------------------------- //

// Support fucntion for end user use if needed. 
// Not used in handbook code.
let rec choose t =
    match t with
    | Empty ->
        failwith "choose: completely undefined function"
    | Leaf (_, l) ->
        // NOTE : This will fail (crash) when 'l' is an empty list!
        List.head l
    | Branch (b, p, t1, t2) ->
        choose t1

// ------------------------------------------------------------------------- //
// Install a (trivial) printer for finite partial functions.                 //
// ------------------------------------------------------------------------- //

//let print_fpf (f : func<'a,'b>) = printf "<func>"

// ------------------------------------------------------------------------- //
// Related stuff for standard functions.                                     //
// ------------------------------------------------------------------------- //

let valmod a y f x =
    if x = a then y
    else f x
    
// In a non-functional world you can create a list of values and
// initialize the list signifiying nothing. e.g. []
// Then when you process the list it could return without exception
// or if you wanted the processing of the list to return with
// exception when there is nothing in the list, you would check
// the list for nothing and return an exception.
//
// In a functinal world you can create a list of functions and
// initialize the list with a function causing an exception given that
// the items is the list are evaluated as functions.
// 
// undef is that function which is used to initialize a list to
// cause an exception if the list is empty when evaluated.
let undef x =
    failwith "undefined function"
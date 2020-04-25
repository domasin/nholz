[<AutoOpen>]
module HOL.GenericTree

type 'a Tree = Tree of 'a * 'a Tree list

type 'a Path = 
    | Top 
    | NodePath of 'a * 'a Tree list * 'a Path * 'a Tree list

type 'a Location = Loc of 'a Tree * 'a Path

let mkTree v xs = Tree(v,xs)

let left (Loc(t, p)) = 
    match p with
    | Top -> failwith "left at top"
    | NodePath(v,l::left, up, right) -> Loc(l, NodePath(v,left, up, t::right))
    | NodePath(v,[], up, right) -> failwith "left of first"

let right (Loc(t, p)) = 
    match p with 
    | Top -> failwith "right at top"
    | NodePath(v,left, up, r::right) -> Loc(r, NodePath(v,t::left, up, right))
    | _ -> failwith "right of last"

let down (Loc(t, p)) = 
    match t with
    | Tree(_,[]) -> failwith "down with Tree"
    | Tree(v,t1::trees) -> Loc(t1, NodePath(v,[], p, trees))

let up (Loc(t,p)) = 
    match p with
    | Top -> failwith "up of top"
    | NodePath(v,left,up,right) -> 
        Loc(Tree(v, ((left |> List.rev)@[t]) @ right),up)

let rec root (Loc (t, p) as l) = 
    match p with 
    | Top -> t
    | _ -> root (up l) 

let zipper t = Loc(t, Top)

let change t (Loc(_, p)) = Loc(t, p)

let insert_right r (Loc(t, p)) = 
    match p with
    | Top -> failwith "insert at top"
    | NodePath(v,left, up, right) -> Loc(t, NodePath(v,left, up, r::right))

let insert_left l (Loc(t, p)) =
    match p with
    | Top -> failwith "insert at top"
    | NodePath(v,left, up, right) -> Loc(t, NodePath(v,l::left, up, right))

let insert_down t1 (Loc(t, p)) = 
    match t with
    | Tree (v,[]) -> Loc(t1, NodePath(v,[], p, []))
    | Tree(v,ss) -> failwith "non empty"

let delete (Loc(_, p)) =
    match p with 
    | Top -> failwith "delete at top"
    | NodePath(v,left, up, r::right) -> Loc(r, NodePath(v,left, up, right))
    | NodePath(v,l::left, up, []) -> Loc(l, NodePath(v,left, up, []))
    | NodePath(v,[], up, []) -> Loc(Tree (v,[]), up)

let rec findNodePath (x:'a) (zipper:'a Location) =
    let (Loc(Tree(value,NodePaths), path)) = zipper
    if value = x then Some zipper
    else
        match NodePaths with
        | [] -> 
            //printf " |> right "
            match path with
            | NodePath(v,left,up,[]) -> None
            | _ -> zipper |> right |> (findNodePath x)
        | _ ->
            //printf " |> down "
            let down = zipper |> down |> findNodePath x
            match down with
            | Some x -> Some x
            | None -> 
                //printfn " |> right "
                zipper |> right |> (findNodePath x)
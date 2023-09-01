let rec sumBools acc y xs = 
    match xs with
    | []-> acc
    | x::xs' -> 
        let carry = x && y
        let sum = x = (not y)
        sumBools (acc@[sum]) carry xs'

let boolList n = 
    let rec boolAux acc start nn = 
        // printfn "boolAux %A %A %i" acc start nn 
        match nn with
        | 1 -> acc |> List.rev
        | _ -> 
            let xs = start |> sumBools [] true
            boolAux ((xs |> List.rev)::acc) xs (nn-1)
    let start = 
        [1..n]
        |> List.map (fun _ -> false)
    start::(boolAux [] start ((2.** n) |> int))

boolList 4

[true; true; false]
|> sumBools [] true
|> sumBools [] true
|> sumBools [] true
|> sumBools [] true

let x,y,z = true,true,false

let carry = (x && y) || ((x || y) && z) 
// let sum = halfsum (halfsum x y) z


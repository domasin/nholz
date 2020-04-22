#load "avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load

let linearize (tr: Proof Tree) = 

    let rec treeToList acc (tr: Proof Tree) = 
        match tr with
        | Tree(x,[]) -> acc@[x,[]]
        | Tree(x,xs) -> 
            xs
            |> List.map (fun x -> x |> treeToList acc)
            |> List.concat
            |> fun lst -> lst@[x,xs |> List.map (fun (Tree(e,_)) -> e)]

    let remapChild (xs:(Proof * Proof list) list) = 
        let indexed = xs |> List.mapi (fun i x -> (i,x))
        indexed 
        |> List.map (fun (i,((e,l,f),cs)) -> (i,((e,l,f),cs |> List.map (fun (c,_,_) -> 
                        indexed 
                        |> List.filter (fun (i',((e',_,_),_)) -> e' = c && i' < i) 
                        |> List.map (fun (i',(_,_)) -> i') 
                        |> List.rev |> List.head))))
    tr
    |> treeToList []
    |> remapChild

([],@"~ true <=> false")
|> start_proof
(* |- ~ true <=> false         *)
|> deduct_antisym_rule_bk [] []
    (* false |- ~ true             *)
    |> contr_rule_bk
        |> assume_rule_bk
    (* ~ true |- false             *)
    |> eq_mp_rule_bk [0] [] "true"
            (* ~ true |- true <=> false    *)
            |> eqf_intro_rule_bk
                |> assume_rule_bk
            (* |- true  *)
            |> by truth_thm "truth\_thm"
|> root
|> linearize

//[
//(0, ((Te `~ true`, "", NullFun), [])); (1, ((Te `false`, "", NullFun), []));
//(2, ((Th false |- false, "assume_rule", TmFn <fun:assume_rule_bk@590>), [1]));
//(3, ((Th false |- ~ true, "contr_rule", TmThmFn <fun:contr_rule_bk@618>),[0; 2])); 
//(4, ((Te `~ true`, "", NullFun), []));
//(5, ((Th ~ true |- ~ true, "assume_rule", TmFn <fun:assume_rule_bk@590>), [4]));
//(6, ((Th ~ true |- true <=> false, "eqf_intro_rule", ThmFn <fun:eqf_intro_rule_bk@633>), [5]));
//(7, ((Th |- true, "truth\_thm", NullFun), []));
//(8, ((Th ~ true |- false, "eq_mp_rule", ThmThmFn <fun:eq_mp_rule_bk@577>),[6; 7]));
//(9, ((Th |- ~ true <=> false, "deduct_antisym_rule", ThmThmFn <fun:deduct_antisym_rule_bk@605>), [3; 8]))
//]
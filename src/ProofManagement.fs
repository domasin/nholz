[<AutoOpen>]
module HOL.ProofManagement

let start_proof (xs,s) = 
    let asl = xs |> List.map (fun x -> x |> parse_term)
    let (tr:Proof Tree) = mkTree(Goal (asl,(s |> parse_term)), "",NullFun) []
    tr |> zipper (*|> fun x -> if !showProof then view x else x*)

let prove' (loc:Proof Location) = 
    let (Loc(Tree((ex,label,just_fn),children), path)) = loc

    match ex with
    | Goal(asl,t) ->
        let child = (Loc (Tree ((Goal (asl,t), label,just_fn),children),path)) |> down
        
        match just_fn with
        | TmFn f -> 
            match child with
            | (Loc (Tree ((Te t, "", NullFun),[]),p)) -> 
                loc |> change (Tree ((Th (f t), label, just_fn),children))
            | _ -> failwith "child is not term"
        | ThmFn f -> 
            match child with
            | (Loc (Tree ((Th t, _, _),_),_)) -> 
                loc |> change (Tree ((Th (f t), label, just_fn),children))
            | _ -> failwith "child is not thm"
        | ThmThmFn f -> 
            let child2 = child |> right
            match child with
            | (Loc (Tree ((Th t, _, _),_),_)) -> 
                match child2 with
                | (Loc (Tree ((Th t2, _, _),_),_)) -> 
                    loc |> change (Tree ((Th (f t t2), label, just_fn),children))
                | _ -> failwith "child2 is not thm"
            | _ -> failwith "child1 is not thm"
        | ThmThmThmFn f -> 
            let child2 = child |> right
            let child3 = child2 |> right
            match child with
            | (Loc (Tree ((Th t, _, _),_),_)) -> 
                match child2 with
                | (Loc (Tree ((Th t2, _, _),_),_)) -> 
                    match child3 with
                    | (Loc (Tree ((Th t3, _, _),_),_)) -> 
                        loc |> change (Tree ((Th (f t t2 t3), label, just_fn),children))
                    | _ -> failwith "child3 is not thm"
                | _ -> failwith "child2 is not thm"
            | _ -> failwith "child1 is not thm"
        | TmThmThmFn f -> 
            let child2 = child |> right
            let child3 = child2 |> right
            match child with
            | (Loc (Tree ((Te t, _, _),_),_)) -> 
                match child2 with
                | (Loc (Tree ((Th t2, _, _),_),_)) -> 
                    match child3 with
                    | (Loc (Tree ((Th t3, _, _),_),_)) -> 
                        loc |> change (Tree ((Th (f t t2 t3), label, just_fn),children))
                    | _ -> failwith "child3 is not thm"
                | _ -> failwith "child2 is not thm"
            | _ -> failwith "child1 is not tm"
        | TmThmFn f -> 
            let child2 = child |> right
            match child with
            | (Loc (Tree ((Te t, _, _),_),_)) -> 
                match child2 with
                | (Loc (Tree ((Th t2, _, _),_),_)) -> 
                    loc |> change (Tree ((Th (f t t2), label, just_fn),children))
                | _ -> failwith "child2 is not thm"
            | _ -> failwith "child1 is not tm"
        | ThmTmFn f -> 
            let child2 = child |> right
            match child with
            | (Loc (Tree ((Th t, _, _),_),_)) -> 
                match child2 with
                | (Loc (Tree ((Te t2, _, _),_),_)) -> 
                    loc |> change (Tree ((Th (f t t2), label, just_fn),children))
                | _ -> failwith "child2 is not tm"
            | _ -> failwith "child1 is not thm"
        | TmLstThmFn f -> 
            let child2 = child |> right
            match child with
            | (Loc (Tree ((TeLst t, _, _),_),_)) -> 
                match child2 with
                | (Loc (Tree ((Th t2, _, _),_),_)) -> 
                    loc |> change (Tree ((Th (f t t2), label, just_fn),children))
                | _ -> failwith "child2 is not thm"
            | _ -> failwith "child1 is not tm"
        | InstTyLstThmFn f -> 
            let child2 = child |> right
            match child with
            | (Loc (Tree ((InstTyLst t, _, _),_),_)) -> 
                match child2 with
                | (Loc (Tree ((Th t2, _, _),_),_)) -> 
                    loc |> change (Tree ((Th (f t t2), label, just_fn),children))
                | _ -> failwith "child2 is not thm"
            | _ -> failwith "child1 is not tm"
        | InstTmLstThmFn f -> 
            let child2 = child |> right
            match child with
            | (Loc (Tree ((InstTmLst t, _, _),_),_)) -> 
                match child2 with
                | (Loc (Tree ((Th t2, _, _),_),_)) -> 
                    loc |> change (Tree ((Th (f t t2), label, just_fn),children))
                | _ -> failwith "child2 is not thm"
            | _ -> failwith "child1 is not tm list"
        | ThmLstFn f -> failwith "ThmLstFn prove not implemented"
        | NullFun -> failwith "no rule given"
        
    | _ -> failwith "not a goal"

let focus_goal (loc:Proof Location) = 
    let exp = loc |> loc_goal |> Option.get
    match exp with
    | (Goal(asl,t)) -> 
        let (tr:Proof Tree) = mkTree(Goal(asl,t),"",NullFun) []
        tr |> zipper 
    | _ -> failwith "focus_goal"

let rec prove (loc:Proof Location) = 
    let newLoc = 
        try
            loc |> lower |> prove' |> prove
        with _ -> loc
    try
        if newLoc |> exp |> is_goal then newLoc
        elif newLoc |> right |> exp |> is_goal then newLoc |> right
        else newLoc |> prove
    with _ -> newLoc

let rec findExp x (loc:Proof Location) =
    let (Loc(Tree((exp,_,_),NodePaths), path)) = loc
    if exp = x then Some loc
    else
        match NodePaths with
        | [] -> 
            //printf "%s" (exp |> printExp)
            //printf " |> right "
            match path with
            | NodePath(v,left,up,[]) -> None
            | _ -> loc |> right |> (findExp x)
        | _ ->
            //printf "%s" (exp |> printExp)
            //printf " |> down "
            let down = loc |> down |> findExp x
            match down with
            | Some x -> Some x
            | None -> 
                //printf "%s" (exp |> printExp)
                //printfn " |> right "
                loc |> right |> (findExp x)

let select exp loc = (findExp exp loc) |> Option.get

let thm_fd lbl th = 
    let (tr: Proof Tree) = mkTree(Th th, lbl, NullFun) []
    tr

let term_fd t = 
    mkTree(Te t, "", NullFun) []

let termlst_fd xs = 
    mkTree(TeLst xs, "", NullFun) []

let instTermlst_fd xs = 
    mkTree(InstTmLst xs, "", NullFun) []

let instTyLst_fd t = 
    mkTree(InstTyLst t, "", NullFun) []

let by thm lbl loc = 
    loc
    |> change (thm |> thm_fd lbl)
    |> prove

let tmFnForward lbl jf t = 
    match jf with
    | TmFn f -> 
        let th = t |> f
        let (tr:Proof Tree) = mkTree (Th th,lbl,TmFn f) [mkTree (Te t,"",NullFun) []]
        tr
    | _ -> failwith "not TmFn"

let thmFnForward lbl jf t = 
    match jf with
    | ThmFn f -> 
        let th = t |> zipper |> loc_thm |> Option.get |> f
        let (tr:Proof Tree) = mkTree (Th th,lbl,ThmFn f) [t]
        tr
    | _ -> failwith "not ThmFn"

let thmThmFnForward lbl jf t1 t2 = 
    match jf with
    | ThmThmFn f -> 
        let th1 = t1 |> zipper |> loc_thm |> Option.get
        let th2 = t2 |> zipper |> loc_thm |> Option.get
        let th = f th1 th2
        let (tr:Proof Tree) = 
            mkTree 
                (Th th,lbl,ThmThmFn f) 
                [t1; t2]
        tr
    | _ -> failwith "not ThmFn"

let thmThmThmFnForward lbl jf t1 t2 t3 = 
    match jf with
    | ThmThmThmFn f -> 
        let th1 = t1 |> zipper |> loc_thm |> Option.get
        let th2 = t2 |> zipper |> loc_thm |> Option.get
        let th3 = t3 |> zipper |> loc_thm |> Option.get
        let th = f th1 th2 th3
        let (tr:Proof Tree) = 
            mkTree 
                (Th th,lbl,ThmThmThmFn f) 
                [t1; t2; t3]
        tr
    | _ -> failwith "not ThmFn"

let TmThmThmFnFnForward lbl jf t1 t2 t3 = 
    match jf with
    | TmThmThmFn f -> 
        let th2 = t2 |> zipper |> loc_thm |> Option.get
        let th3 = t3 |> zipper |> loc_thm |> Option.get
        let th = f t1 th2 th3
        let (tr:Proof Tree) = 
            mkTree 
                (Th th,lbl,TmThmThmFn f) 
                [t1 |> term_fd; t2; t3]
        tr
    | _ -> failwith "not ThmFn"

let tmThmFnForward lbl jf t t2 = 
    match jf with
    | TmThmFn f -> 
        let th2 = t2 |> zipper |> loc_thm |> Option.get
        let th = f t th2
        let (tr:Proof Tree) = 
            mkTree 
                (Th th,lbl,TmThmFn f) 
                [t |> term_fd; t2]
        tr
    | _ -> failwith "not ThmFn"

let thmTmFnForward lbl jf tr1 t = 
    match jf with
    | ThmTmFn f -> 
        let th1 = tr1 |> zipper |> loc_thm |> Option.get
        let th = f th1 t
        let (tr:Proof Tree) = 
            mkTree 
                (Th th,lbl,ThmTmFn f) 
                [tr1; t |> term_fd]
        tr
    | _ -> failwith "not ThmFn"

let TmLstThmFnForward lbl jf xs t2 = 
    match jf with
    | TmLstThmFn f -> 
        let th2 = t2 |> zipper |> loc_thm |> Option.get
        //let tlst = xs |> List.map (fun x -> x |> parse_term)
        let th = f xs th2
        let (tr:Proof Tree) = 
            mkTree 
                (Th th,lbl,TmLstThmFn f) 
                [xs |> termlst_fd; t2]
        tr
    | _ -> failwith "not ThmFn"

let InstTmLstThmFnForward lbl jf xs t2 = 
    match jf with
    | InstTmLstThmFn f -> 
        let th2 = t2 |> zipper |> loc_thm |> Option.get
        //let tlst = xs |> List.map (fun x -> x |> parse_term)
        let th = f xs th2
        let (tr:Proof Tree) = 
            mkTree 
                (Th th,lbl,InstTmLstThmFn f) 
                [xs |> instTermlst_fd; t2]
        tr
    | _ -> failwith "not ThmFn"

let ThmLstFnForward lbl jf xs = 
    match jf with
    | ThmLstFn f -> 
        let th = f (xs |> List.map (fun x -> x |> zipper |> loc_thm |> Option.get))
        let (tr:Proof Tree) = 
            mkTree 
                (Th th,lbl,ThmLstFn f) xs
        tr
    | _ -> failwith "not ThmFn"

let instTyLstThmFnForward lbl jf xs t2 = 
    match jf with
    | InstTyLstThmFn f -> 
        let th2 = t2 |> zipper |> loc_thm |> Option.get
        let th = f xs th2
        let (tr:Proof Tree) = 
            mkTree 
                (Th th,lbl,InstTyLstThmFn f) 
                [xs |> instTyLst_fd; t2]
        tr
    | _ -> failwith "not ThmFn"

let refl_conv_fd t = tmFnForward "refl_conv" (TmFn refl_conv) t

let refl_conv_bk = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t) ->
            let (ant,_) = dest_eq t
            loc
            |> change (Tree ((Goal (asl,t), "refl_conv", TmFn refl_conv),children))
            |> insert_down (mkTree((Te ant),"", NullFun) []) 
            |> prove
        | _ -> failwith "not a goal"

// TODO beta_conv

// TODO mk_comb_rule

let mk_abs_rule_fd = tmThmFnForward "mk_abs_rule" (TmThmFn mk_abs_rule)

let mk_abs_rule_bk loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let (t1',t2') = dest_eq t
        let (x,t1) = t1' |> dest_abs
        let (_,t2) = t2' |> dest_abs
        let eqTm = mk_eq (t1,t2) 
        loc
        |> change (Tree ((Goal (asl,t), "mk_abs_rule", TmThmFn mk_abs_rule),children))
        |> insert_down (mkTree(Te x, "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl,eqTm), "", NullFun) []) 
        |> right
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

let assume_rule_fd t = tmFnForward "assume_rule" (TmFn assume_rule) t

let assume_rule_bk = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(xs,t) when xs = [t] ->
            loc
            |> change (Tree ((ex, "assume_rule", TmFn assume_rule),children))
            |> insert_down (mkTree((Te t),"", NullFun) []) 
            |> prove
        | _ -> failwith "can't apply rule"

let disch_rule_fd = tmThmFnForward "disch_rule" (TmThmFn disch_rule)

let disch_rule_bk = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t)  ->
            let (t1,t2) = dest_imp t
            let asl2 = asl |> List.filter (fun x -> x <> t1)
            loc
            |> change (Tree ((ex, "disch_rule", TmThmFn disch_rule),children))
            |> insert_down (mkTree((Te t1),"", NullFun) []) 
            |> insert_right (mkTree(Goal (asl2@[t1],t2),"", NullFun) []) 
            |> right
        | _ -> failwith "can't apply rule"

let mp_rule_fd t1 t2 = thmThmFnForward "eq_mp_rule" (ThmThmFn mp_rule) t1 t2

let mp_rule_bk ind1 ind2 t2 = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t) ->
            let asl1 = ind1 |> List.map (fun x -> asl.[x])
            let asl2 = ind2 |> List.map (fun x -> asl.[x])
            let t2' = t2 |> parse_term
            let g1 = Goal(asl1, mk_imp (t2',t))
            let g2 = Goal(asl2, t2')
            loc
            |> change (Tree ((Goal (asl,t), "mp_rule", ThmThmFn mp_rule),children))
            |> insert_down (mkTree(g1, "", NullFun) []) 
            |> insert_right (mkTree(g2, "", NullFun) []) 
        | _ -> failwith "not a goal"

let eq_mp_rule_fd t1 t2 = thmThmFnForward "eq_mp_rule" (ThmThmFn eq_mp_rule) t1 t2

let eq_mp_rule_bk ind1 ind2 t2 = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t) ->
            let asl1 = ind1 |> List.map (fun x -> asl.[x])
            let asl2 = ind2 |> List.map (fun x -> asl.[x])
            let t2' = t2 |> parse_term
            let g1 = Goal(asl1, mk_eq (t2',t))
            let g2 = Goal(asl2, t2')
            loc
            |> change (Tree ((Goal (asl,t), "eq_mp_rule", ThmThmFn eq_mp_rule),children))
            |> insert_down (mkTree(g1, "", NullFun) []) 
            |> insert_right (mkTree(g2, "", NullFun) []) 
        | _ -> failwith "not a goal"

let inst_rule_fd = InstTmLstThmFnForward "inst_rule" (InstTmLstThmFn inst_rule)

let inst_rule_bk theta loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let newGoal =
            let c' = try2 (var_inst theta) t         "inst_rule_bk" in
            let hs' = setify' alpha_eq (map (var_inst theta) asl) in
            Goal (hs',c')
        let theta2 = theta |> List.map (fun (x,y) -> (y,x))
        loc
        |> change (Tree ((Goal (asl,t), "inst_rule", InstTmLstThmFn inst_rule),children))
        |> insert_down (mkTree(InstTmLst theta2, "", NullFun) []) 
        |> insert_right (mkTree(newGoal, "", NullFun) []) 
        |> right
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

let inst_type_rule_fd xs = instTyLstThmFnForward "inst_type_rule" (InstTyLstThmFn inst_type_rule) xs

// TODO inst_type_rule_bk

let mk_comb1_rule_fd = thmTmFnForward "mk_comb1_rule" (ThmTmFn mk_comb1_rule)

let mk_comb1_rule_bk loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let (t1,t2) = t |> dest_eq
        let (t11,x) = t1 |> dest_comb
        let (t21,_) = t2 |> dest_comb
        let tg = mk_eq (t11,t21)
        loc
        |> change (Tree ((Goal (asl,t), "mk_comb1_rule", ThmTmFn mk_comb1_rule),children))
        |> insert_down (mkTree(Goal(asl,tg), "", NullFun) []) 
        |> insert_right (mkTree(Te x, "", NullFun) []) 
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

let mk_comb2_rule_fd = tmThmFnForward "mk_comb2_rule" (TmThmFn mk_comb2_rule)

let mk_comb2_rule_bk loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let (t1,t2) = t |> dest_eq
        let (x,t11) = t1 |> dest_comb
        let (_,t21) = t2 |> dest_comb
        let tg = mk_eq (t11,t21)
        loc
        |> change (Tree ((Goal (asl,t), "mk_comb2_rule", TmThmFn mk_comb2_rule),children))
        |> insert_down (mkTree(Te x, "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl,tg), "", NullFun) [])  
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

let trans_rule_fd = thmThmFnForward "trans_rule" (ThmThmFn trans_rule)

let trans_rule_bk t' loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let (t11,t22) = dest_eq t
        let mt = t' |> parse_term
        let t1 = mk_eq(t11,mt)
        let t2 = mk_eq(mt,t22)
        loc
        |> change (Tree ((Goal (asl,t), "trans_rule", ThmThmFn trans_rule),children))
        |> insert_down (mkTree(Goal(asl,t1), "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl,t2), "", NullFun) []) 
        
    | _ -> failwith "not a goal"

let list_trans_rule_fd = ThmLstFnForward "list_trans_rule" (ThmLstFn list_trans_rule)
// TODO list_trans_rule_bk

let sym_rule_fd = thmFnForward "sym_rule" (ThmFn sym_rule)

let sym_rule_bk = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t) ->
            let (t1,t2) = dest_eq t
            let g1 = Goal (asl,(mk_eq (t2,t1)))
            loc
            |> change (Tree ((Goal (asl,t), "sym_rule", ThmFn sym_rule),children))
            |> insert_down (mkTree(g1, "", NullFun) []) 
        | _ -> failwith "not a goal"

// TODO app_beta_rhs_rule
// TODO list_app_beta_rhs_rule
// TODO app_beta_rule
// TODO list_app_beta_rule
// TODO alpha_link_conv
// TODO alpha_conv
// TODO subs_conv
// TODO subs_rule
// TODO subst_conv
// TODO subst_rule
// TODO conv_rule
// TODO eqt_elim_rule

let undisch_rule_fd = thmFnForward "undisch_rule" (ThmFn undisch_rule)

let undisch_rule_bk ind = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t)  ->
            let asl' = asl.[ind]
            let t1 = mk_imp (asl',t)
            let asl2 = asl |> List.filter (fun x -> x <> asl')
            loc
            |> change (Tree ((ex, "undisch_rule", ThmFn undisch_rule),children))
            |> insert_down (mkTree(Goal (asl2,t1),"", NullFun) []) 
        | _ -> failwith "can't apply rule"

let add_asm_rule_fd = tmThmFnForward "add_asm_rule" (TmThmFn add_asm_rule)

let add_asm_rule_bk ind (loc: Proof Location) = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let t1 = asl.[ind]
        let asl1 = asl |> List.filter (fun x -> x <> t1)
        loc
        |> change (Tree ((Goal (asl,t), "add_asm_rule", TmThmFn add_asm_rule),children))
        |> insert_down (mkTree(Te t1, "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl1,t), "", NullFun) []) 
        |> right
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

// TODO prove_asm_rule
// TODO eq_imp_rule1
// TODO eq_imp_rule2

let not_intro_rule_fd = thmFnForward "not_intro_rule" (ThmFn not_intro_rule)

let not_intro_rule_bk = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t)  ->
            let t1 = mk_imp (dest_not t,false_tm)
            loc
            |> change (Tree ((ex, "not_intro_rule", ThmFn not_intro_rule),children))
            |> insert_down (mkTree(Goal (asl,t1),"", NullFun) [])   
            //|> fun x -> if !showProof then view x else x
        | _ -> failwith "can't apply rule"

let not_elim_rule_fd = thmFnForward "not_elim_rule" (ThmFn not_elim_rule)

let not_elim_rule_bk = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t) ->
            let (t1,_) = t |> dest_imp 
            let g1 = Goal (asl,t1 |> mk_not)
            loc
            |> change (Tree ((Goal (asl,t), "not_elim_rule", ThmFn not_elim_rule),children))
            |> insert_down (mkTree(g1, "", NullFun) []) 
        | _ -> failwith "not a goal"

let deduct_contrapos_rule_fd = tmThmFnForward "deduct_contrapos_rule" (TmThmFn deduct_contrapos_rule)

let deduct_contrapos_rule_bk ind loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let t1 = t |> dest_not
        let t2 = asl.[ind] |> dest_not
        let asl2 = (asl |> List.filter (fun x -> x <> asl.[ind]))@[t1]
        loc
        |> change (Tree ((Goal (asl,t), "deduct_contrapos_rule", TmThmFn deduct_contrapos_rule),children))
        |> insert_down (mkTree(Te t1, "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl2,t2), "", NullFun) []) 
        |> right
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

let eqf_elim_rule_fd = thmFnForward "eqf_elim_rule" (ThmFn eqf_elim_rule)

let eqf_elim_rule_bk = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t) ->
            let t1 = mk_eq (t |> dest_not,false_tm)
            let g1 = Goal (asl,t1)
            loc
            |> change (Tree ((Goal (asl,t), "eqf_elim_rule", ThmFn eqf_elim_rule),children))
            |> insert_down (mkTree(g1, "", NullFun) []) 
        | _ -> failwith "not a goal"

// TODO imp_trans_rule
// TODO list_imp_trans_rule

let spec_rule_fd = tmThmFnForward "spec_rule" (TmThmFn spec_rule)

let spec_rule_bk tx loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let t2 = mk_forall (tx,t)
        loc
        |> change (Tree ((Goal (asl,t), "spec_rule", TmThmFn spec_rule),children))
        |> insert_down (mkTree(Te tx, "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl,t2), "", NullFun) []) 
        |> right
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

let list_spec_rule_fd = TmLstThmFnForward "list_spec_rule" (TmLstThmFn list_spec_rule)
// TODO list_spec_rule_bk

// TODO spec_all_rule
// TODO bspec_rule

let contr_rule_fd = tmThmFnForward "contr_rule" (TmThmFn contr_rule)

let contr_rule_bk loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        loc
        |> change (Tree ((Goal (asl,t), "contr_rule", TmThmFn contr_rule),children))
        |> insert_down (mkTree(Te t, "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl,("false" |> parse_term)), "", NullFun) []) 
        |> right
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

let eta_conv_fd t = tmFnForward "eta_conv" (TmFn eta_conv) t

let eta_conv_bk = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t) ->
            let (ant,_) = dest_eq t
            loc
            |> change (Tree ((Goal (asl,t), "eta_conv", TmFn eta_conv),children))
            |> insert_down (mkTree((Te ant),"", NullFun) []) 
            |> prove
        | _ -> failwith "not a goal"

// TODO imp_antisym_rule

let deduct_antisym_rule_fd t1 t2 = thmThmFnForward "deduct_antisym_rule" (ThmThmFn deduct_antisym_rule) t1 t2

let deduct_antisym_rule_bk ind1 ind2 loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let asl1 = ind1 |> List.map (fun x -> asl.[x])
        let asl2 = ind2 |> List.map (fun x -> asl.[x])
        let (t1,t2) = dest_eq t
        loc
        |> change (Tree ((Goal (asl,t), "deduct_antisym_rule", ThmThmFn deduct_antisym_rule),children))
        |> insert_down (mkTree(Goal(asl1@[t2],t1), "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl2@[t1],t2), "", NullFun) []) 
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

// TODO sym_conv

let eqt_intro_rule_fd = thmFnForward "eqt_intro_rule" (ThmFn eqt_intro_rule)

let eqt_intro_rule_bk = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t) ->
            let (t1,_) = t |> dest_eq
            let g1 = Goal (asl,t1)
            loc
            |> change (Tree ((Goal (asl,t), "eqt_intro_rule", ThmFn eqt_intro_rule),children))
            |> insert_down (mkTree(g1, "", NullFun) []) 
        | _ -> failwith "not a goal"

let eqf_intro_rule_fd = thmFnForward "eqf_intro_rule" (ThmFn eqf_intro_rule)

let eqf_intro_rule_bk loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let (t1,t2) = dest_eq t
        loc
        |> change (Tree ((Goal (asl,t), "eqf_intro_rule", ThmFn eqf_intro_rule),children))
        |> insert_down (mkTree(Goal(asl,t1 |> mk_not), "", NullFun) []) 
    | _ -> failwith "not a goal"

let gen_rule_fd = tmThmFnForward "gen_rule" (TmThmFn gen_rule)

let gen_rule_bk loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let (x,t') = t |> dest_forall
        loc
        |> change (Tree ((Goal (asl,t), "gen_rule", TmThmFn gen_rule),children))
        |> insert_down (mkTree(Te x, "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl,t'), "", NullFun) []) 
        |> right
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

let list_gen_rule_fd = TmLstThmFnForward "list_gen_rule" (TmLstThmFn list_gen_rule)

let list_gen_rule_bk loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let (vv,t1) = t |> strip_forall
        loc
        |> change (Tree ((Goal (asl,t), "list_gen_rule", TmLstThmFn list_gen_rule),children))
        |> insert_down (mkTree(TeLst vv, "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl,t1), "", NullFun) []) 
        |> right
    | _ -> failwith "not a goal"

let conj_rule_fd = thmThmFnForward "conj_rule" (ThmThmFn conj_rule)

let conj_rule_bk ind1 ind2 loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let asl1 = ind1 |> List.map (fun x -> asl.[x])
        let asl2 = ind2 |> List.map (fun x -> asl.[x])
        let (t1,t2) = t |> dest_conj
        loc
        |> change (Tree ((Goal (asl,t), "conj_rule", ThmThmFn conj_rule),children))
        |> insert_down (mkTree(Goal(asl1,t1), "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl2,t2), "", NullFun) []) 
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

let conjunct1_rule_fd = thmFnForward "conjunct1_rule" (ThmFn conjunct1_rule)

let conjunct1_rule_bk t2 = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t) ->
            let g1 = Goal (asl,mk_conj (t, t2 |> parse_term))
            loc
            |> change (Tree ((Goal (asl,t), "conjunct1_rule", ThmFn conjunct1_rule),children))
            |> insert_down (mkTree(g1, "", NullFun) []) 
        | _ -> failwith "not a goal"

let conjunct2_rule_fd = thmFnForward "conjunct2_rule" (ThmFn conjunct2_rule)

let conjunct2_rule_bk t1 = 
    fun (loc: Proof Location) -> 
        let (Loc(Tree((ex,_,_),children), _)) = loc
        match ex with
        | Goal(asl,t) ->
            let g1 = Goal (asl,mk_conj (t1 |> parse_term, t))
            loc
            |> change (Tree ((Goal (asl,t), "conjunct2_rule", ThmFn conjunct2_rule),children))
            |> insert_down (mkTree(g1, "", NullFun) []) 
        | _ -> failwith "not a goal"

let disj_cases_rule_fd = thmThmThmFnForward "disj_cases_rule" (ThmThmThmFn disj_cases_rule)

let disj_cases_rule_bk ind1 ind2 ind3 disj1 disj2 loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let disj1Tm = (disj1 |> parse_term)
        let disj2Tm = (disj2 |> parse_term)
        let disj = mk_disj (disj1Tm, disj2Tm)
        let asl1 = ind1 |> List.map (fun x -> asl.[x])
        let asl2 = (ind2 |> List.map (fun x -> asl.[x]))@[disj1Tm]
        let asl3 = (ind3 |> List.map (fun x -> asl.[x]))@[disj2Tm]
        loc
        |> change (Tree ((Goal (asl,t), "disj_cases_rule", ThmThmThmFn disj_cases_rule),children))
        |> insert_down (mkTree(Goal (asl1,disj), "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl2,t), "", NullFun) []) 
        |> right
        |> insert_right (mkTree(Goal(asl3,t), "", NullFun) []) 
        |> left
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

let disj1_rule_fd = thmTmFnForward "disj1_rule" (ThmTmFn disj1_rule)

let disj1_rule_bk loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let (t1,t2) = t |> dest_disj
        loc
        |> change (Tree ((Goal (asl,t), "disj1_rule", ThmTmFn disj1_rule),children))
        |> insert_down (mkTree(Goal(asl,t1), "", NullFun) []) 
        |> insert_right (mkTree(Te t2, "", NullFun) []) 
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

let disj2_rule_fd = tmThmFnForward "disj2_rule" (TmThmFn disj2_rule)

let disj2_rule_bk loc = 
    let (Loc(Tree((ex,_,_),children), _)) = loc
    match ex with
    | Goal(asl,t) ->
        let (t1,t2) = t |> dest_disj
        loc
        |> change (Tree ((Goal (asl,t), "disj2_rule", TmThmFn disj2_rule),children))
        |> insert_down (mkTree(Te t1, "", NullFun) []) 
        |> insert_right (mkTree(Goal(asl,t2), "", NullFun) []) 
        |> right
        //|> fun x -> if !showProof then view x else x
    | _ -> failwith "not a goal"

// TODO choose_rule

let mk_bin_rule_fd = TmThmThmFnFnForward "mk_bin_rule" (TmThmThmFn mk_bin_rule)
// TODO mk_bin_rule_bk




#load "avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load

//let true_def_tr = true_def, mkGraph (Th true_def, "true\_def") []

//let th = 
//    (* |- true                        *)
//    eq_mp_rule_tr
//      (* |- (\p. p) = (\p. p) <=> true  *)
//      (sym_rule_tr true_def_tr)
//      (* |- (\p. p) = (\p. p)           *)
//      (refl_conv_tr (parse_term(@"\(p:bool).p")))

//th |> print_graph

let (eq_mp_tac: term -> tactic) =
  fun tm (asl,w) ->
    try 
        let tm1 = mk_eq(tm,w)
        null_meta,[asl, tm1; asl, tm],
        fun _ [th1; th2] -> eq_mp_rule th1 th2
    with Failure _ -> failwith "eq_mp_tac";;

g (parse_term @"true")
e2 (eq_mp_tac (parse_term @"(\(p:bool). p) = (\p. p)"))
e2 (CONV_TAC sym_conv)
e2 (ACCEPT_TAC true_def)
e2 REFL_TAC
top_thm()

let truth_thm_tr = (truth_thm, mkGraph (Th truth_thm, "truth\_thm") [])

let th = 
    (* |- ~ true <=> false         *)
    deduct_antisym_rule_tr
        (* false |- ~ true             *)
        (contr_rule_tr (parse_term(@"~ true")) (assume_rule_tr (parse_term(@"false"))))
        (* ~ true |- false             *)
        (eq_mp_rule_tr
          (* ~ true |- true <=> false    *)
          (eqf_intro_rule_tr (assume_rule_tr (parse_term(@"~ true"))))
           truth_thm_tr )

th |> print_graph

let (deduct_antisym_rule_tac: tactic) =
  fun (asl,w) ->
    let tm1,tm2 = dest_eq w
    let th1 = assume_rule tm1
    let th2 = assume_rule tm2
    try 
        null_meta,[("",th2)::asl, tm1; ("",th1)::asl, tm2],
        fun _ [th1; th2] -> deduct_antisym_rule th1 th2
    with Failure _ -> failwith "deduct_antisym_rule_tac";;

let (CONTR_TAC: thm_tactic) =
  let propagate_thm th i [] = INSTANTIATE_ALL i th in
  fun cth (asl,w) ->
    try let th = contr_rule w cth in
        null_meta,[],propagate_thm th
    with Failure _ -> failwith "CONTR_TAC"

dest_eq (parse_term @"~ true <=> false")

g (parse_term @"~ true <=> false")
e2 deduct_antisym_rule_tac
e2 (CONTR_TAC ("false" |> parse_term |> assume_rule))
e2 (eq_mp_tac ("true" |> parse_term))

//let th1 = (just_fn1:justification) null_inst []

//let (deduct_antisym_tac: tactic) =
//  fun (asl,w) ->
//    try let l,r = dest_eq w in
//        null_meta,[asl, mk_imp(l,r); asl, mk_imp(r,l)],
//        fun _ [th1; th2] -> deduct_antisym_rule th1 th2
//    with Failure _ -> failwith "deduct_antisym_tac";;

//let asl : (string * thm) list = []

//let w = "~ true <=> false " |> parse_term
//let l,r = dest_eq w
//let th1_tm = mk_imp(l,r)
//let th2_tm = mk_imp(r,l)

//let newgoals = [asl, th1_tm; asl, th2_tm]
//let justfn = fun _ [th1; th2] -> deduct_antisym_rule th1 th2

//let (eq_mp_tac: tactic) =
//  fun (asl,w) ->
//    try let l,r = dest_eq w in
//        null_meta,[asl, mk_imp(l,r); asl, mk_imp(r,l)],
//        fun _ [th1; th2] -> eq_mp_rule th1 th2
//    with Failure _ -> failwith "eq_mp_tac";;

//let (imp_antisym_rule_tac: tactic) =
//  fun (asl,w) ->
//    try let l,r = dest_eq w in
//        null_meta,[asl, mk_imp(l,r); asl, mk_imp(r,l)],
//        fun _ [th1; th2] -> imp_antisym_rule th1 th2
//    with Failure _ -> failwith "imp_antisym_rule_tac";;

//let (DISCH_TAC: tactic) =
//  let f_tm = false_tm in
//  fun (asl,w) ->
//    try let ant,c = dest_imp w in
//        let th1 = assume_rule ant in
//        null_meta,[("",th1)::asl,c],
//        fun i [th] -> prim_disch_rule (instantiate i ant) th
//    with Failure _ -> 
//        try
//            let ant = dest_not w in
//            let th1 = assume_rule ant in
//            null_meta,[("",th1)::asl,f_tm],
//            fun i [th] -> not_intro_rule(prim_disch_rule (instantiate i ant) th)
//        with Failure _ -> failwith "DISCH_TAC"

//let (UNDISCH_TAC: term -> tactic) =
// fun tm (asl,w) ->
//   try let sthm,asl' = remove1 (fun (_,asm) -> alpha_eq (concl asm) tm) asl in
//       let thm = snd sthm in
//       null_meta,[asl',mk_imp(tm,w)],
//       fun i [th] -> prim_mp_rule th (INSTANTIATE_ALL i thm)
//   with Failure _ -> failwith "UNDISCH_TAC"

//let goal1:goal = ([], (parse_term @"~ true <=> false"));;
//let (_,goal_list1,just_fn1) = imp_antisym_rule_tac goal1

//let (_,goal_list2,just_fn2) = DISCH_TAC goal_list1.[1]
//let goal3 = ACCEPT_TAC ("false" |> parse_term |> assume_rule) goal_list2.[0]


//let goal2 = UNDISCH_TAC ("false" |> parse_term) goal_list1.[0]

//let th1 = (just_fn1:justification) null_inst []
// experiment porting from hol_light

[<AutoOpen>]
module HOL.Tactics

let null_inst = ([],[],[] :instantiation)

let null_meta = (([]:term list),null_inst)

(* ------------------------------------------------------------------------- *)
(* A goal has labelled assumptions, and the hyps are now thms.               *)
(* ------------------------------------------------------------------------- *)

type goal = (string * thm) list * term

let equals_goal ((a,w):goal) ((a',w'):goal) =
    forall2 (fun (s,th) (s',th') -> s = s' && thm_eq th th') a a' && w = w'

(* ------------------------------------------------------------------------- *)
(* A justification function for a goalstate [A1 ?- g1; ...; An ?- gn],       *)
(* starting from an initial goal A ?- g, is a function f such that for any   *)
(* instantiation @:                                                          *)
(*                                                                           *)
(*   f(@) [A1@ |- g1@; ...; An@ |- gn@] = A@ |- g@                           *)
(* ------------------------------------------------------------------------- *)

type justification = instantiation -> thm list -> thm

(* ------------------------------------------------------------------------- *)
(* The goalstate stores the subgoals, justification, current instantiation,  *)
(* and a list of metavariables.                                              *)
(* ------------------------------------------------------------------------- *)

type goalstate = (term list * instantiation) * goal list * justification

(* ------------------------------------------------------------------------- *)
(* A goalstack is just a list of goalstates. Could go for more...            *)
(* ------------------------------------------------------------------------- *)

type goalstack = goalstate list

(* ------------------------------------------------------------------------- *)
(* A refinement, applied to a goalstate [A1 ?- g1; ...; An ?- gn]            *)
(* yields a new goalstate with updated justification function, to            *)
(* give a possibly-more-instantiated version of the initial goal.            *)
(* ------------------------------------------------------------------------- *)

type refinement = goalstate -> goalstate

(* ------------------------------------------------------------------------- *)
(* A tactic, applied to a goal A ?- g, returns:                              *)
(*                                                                           *)
(*  o A list of new metavariables introduced                                 *)
(*  o An instantiation (%)                                                   *)
(*  o A list of subgoals                                                     *)
(*  o A justification f such that for any instantiation @ we have            *)
(*    f(@) [A1@  |- g1@; ...; An@ |- gn@] = A(%;@) |- g(%;@)                 *)
(* ------------------------------------------------------------------------- *)

type tactic = goal -> goalstate

type thm_tactic = thm -> tactic

type thm_tactical = thm_tactic -> thm_tactic

(* ------------------------------------------------------------------------- *)
(* Apply instantiation to a goal.                                            *)
(* ------------------------------------------------------------------------- *)

let (inst_goal:instantiation->goal->goal) =
  fun p (thms,w) ->
    map (id ||>> INSTANTIATE_ALL p) thms,instantiate p w

(* ------------------------------------------------------------------------- *)
(* Perform a sequential composition (left first) of instantiations.          *)
(* ------------------------------------------------------------------------- *)

let (compose_insts :instantiation->instantiation->instantiation) =
  fun (pats1,tmin1,tyin1) ((pats2,tmin2,tyin2) as i2) ->
    let tmin = map (instantiate i2 ||>> tyvar_inst tyin2) tmin1
    let tyin = map (type_inst tyin2 ||>> id) tyin1 in
    let tmin' = filter (fun (_,x) -> not (can (rev_assoc x) tmin)) tmin2
    let tyin' = filter (fun (_,a) -> not (can (rev_assoc a) tyin)) tyin2 in
    pats1@pats2,tmin@tmin',tyin@tyin'

(* ------------------------------------------------------------------------- *)
(* Construct A,_FALSITY_ |- p; contortion so falsity is the last element.    *)
(* ------------------------------------------------------------------------- *)

//let _FALSITY_ = prim_new_const_definition ("_FALSITY_", parse_term(@"false")) //new_definition(parse_term @"_FALSITY_ = F")

//let mk_fthm =
//    let pth = undisch_rule(eq_imp_rule1 _FALSITY_)
//    let qth = assume_rule (parse_term @"false") in
//    fun (asl,c) -> prove_asm_rule qth (List.foldBack add_asm_rule (rev asl) (contr_rule c pth))

//(* ------------------------------------------------------------------------- *)
//(* Validity checking of tactics. This cannot be 100% accurate without making *)
//(* arbitrary theorems, but "mk_fthm" brings us quite close.                  *)
//(* ------------------------------------------------------------------------- *)

//let (VALID:tactic->tactic) =
//  let fake_thm (asl,w) =
//    let asms = List.foldBack (union << asms << snd) asl [] in
//    mk_fthm(asms,w)
//  let false_tm = (parse_term @"_FALSITY_") in
//  fun tac (asl,w) ->
//    let ((mvs,i),gls,just as res) = tac (asl,w) in
//    let ths = map fake_thm gls in
//    let asl',w' = dest_thm(just null_inst ths) in
//    let asl'',w'' = inst_goal i (asl,w) in
//    let maxasms =
//      List.foldBack (fun (_,th) -> union (insert (concl th) (asms th))) asl'' [] in
//    if alpha_eq w' w'' &&
//       forall (fun t -> exists (alpha_eq t) maxasms) (subtract asl' [false_tm])
//    then res else failwith "VALID: Invalid tactic"

(* ------------------------------------------------------------------------- *)
(* Various simple combinators for tactics, identity tactic etc.              *)
(* ------------------------------------------------------------------------- *)

let (THEN),(THENL) =
    let propagate_empty i [] = []
    let propagate_thm th i [] = INSTANTIATE_ALL i th in
    let compose_justs n just1 just2 i ths =
        let ths1,ths2 = cut n ths in
        (just1 i ths1)::(just2 i ths2) in
    let rec seqapply l1 l2 = 
        match (l1,l2) with
        | ([],[]) -> null_meta,[],propagate_empty
        | ((tac:tactic)::tacs),((goal:goal)::goals) ->
                 let ((mvs1,insts1),gls1,just1) = tac goal in
                 let goals' = map (inst_goal insts1) goals in
                 let ((mvs2,insts2),gls2,just2) = seqapply tacs goals' in
                 ((union mvs1 mvs2,compose_insts insts1 insts2),
                  gls1@gls2,compose_justs (length gls1) just1 just2)
        | _,_ -> failwith "seqapply: Length mismatch" in
    let justsequence just1 just2 insts2 i ths =
        just1 (compose_insts insts2 i) (just2 i ths) in
    let tacsequence ((mvs1,insts1),gls1,just1) tacl =
        let ((mvs2,insts2),gls2,just2) = seqapply tacl gls1 in
        let jst = justsequence just1 just2 insts2 in
        let just = if gls2 = [] then propagate_thm (jst null_inst []) else jst in
        ((union mvs1 mvs2,compose_insts insts1 insts2),gls2,just) in
    let (then_: tactic -> tactic -> tactic) =
        fun tac1 tac2 g ->
            let _,gls,_ as gstate = tac1 g in
            tacsequence gstate (List.replicate (length gls) tac2)
    let (thenl_: tactic -> tactic list -> tactic) =
        fun tac1 tac2l g ->
            let _,gls,_ as gstate = tac1 g in
            if gls = [] then tacsequence gstate []
            else tacsequence gstate tac2l in
    then_,thenl_

let ((ORELSE): tactic -> tactic -> tactic) =
    fun tac1 tac2 g ->
        try tac1 g with Failure _ -> tac2 g

let (FAIL_TAC: string -> tactic) =
    fun tok g -> failwith tok

let (NO_TAC: tactic) =
    FAIL_TAC "NO_TAC"

let (ALL_TAC:tactic) =
    fun g -> null_meta,[g],fun _ [th] -> th

let TRY tac =
    tac |> ORELSE <| ALL_TAC

let rec REPEAT tac g =
    ((tac |> THEN <| REPEAT tac) |> ORELSE <| ALL_TAC) g

/// Sequentially applies all the tactics in a given list of tactics.
let EVERY tacl =
    List.foldBack THEN tacl ALL_TAC

/// Applies the first tactic in a tactic list that succeeds.
let FIRST : tactic list -> tactic =
    fun tacl g -> List.reduceBack ORELSE tacl g

/// Sequentially applies all tactics given by mapping a function over a list.
let MAP_EVERY (tacf : 'T -> tactic) (lst : 'T list) : tactic = 
    EVERY(map tacf lst)

/// Applies first tactic that succeeds in a list given by mapping a function over a list.
let MAP_FIRST tacf lst = FIRST(map tacf lst)

let (CHANGED_TAC: tactic -> tactic) =
    fun tac g ->
        let (meta,gl,_ as gstate) = tac g in
        if meta = null_meta && length gl = 1 && equals_goal (hd gl) g
        then failwith "CHANGED_TAC" else gstate

let rec REPLICATE_TAC n tac =
    if n <= 0 then ALL_TAC else tac |> THEN <| (REPLICATE_TAC (n - 1) tac)

(* ------------------------------------------------------------------------- *)
(* Combinators for theorem continuations / "theorem tacticals".              *)
(* ------------------------------------------------------------------------- *)

/// Composes two theorem-tacticals.
let (THEN_TCL : thm_tactical -> thm_tactical -> thm_tactical) = 
    fun ttcl1 ttcl2 ttac -> ttcl1(ttcl2 ttac)

let ((ORELSE_TCL): thm_tactical -> thm_tactical -> thm_tactical) =
    fun ttcl1 ttcl2 ttac th ->
        try ttcl1 ttac th with Failure _ -> ttcl2 ttac th

/// Repeatedly applies a theorem-tactical until it fails when applied to the theorem.
let rec REPEAT_TCL ttcl ttac th =
    ((ttcl |> THEN_TCL <| (REPEAT_TCL ttcl)) |> ORELSE_TCL <| id) ttac th

let (REPEAT_GTCL: thm_tactical -> thm_tactical) =
    let rec REPEAT_GTCL ttcl ttac th g =
        try ttcl (REPEAT_GTCL ttcl ttac) th g with Failure _ -> ttac th g in
    REPEAT_GTCL

/// Passes a theorem unchanged to a theorem-tactic.
let (ALL_THEN : thm_tactical) = id

let (NO_THEN: thm_tactical) =
    fun ttac th -> failwith "NO_THEN";

/// Composes a list of theorem-tacticals.
let EVERY_TCL ttcll =
    List.foldBack THEN_TCL ttcll ALL_THEN

/// Applies the first theorem-tactical in a list that succeeds.
let FIRST_TCL ttcll =
    List.reduceBack ORELSE_TCL ttcll

(* ------------------------------------------------------------------------- *)
(* Tactics to augment assumption list. Note that to allow "ASSUME p" for     *)
(* any assumption "p", these add a PROVE_HYP in the justification function,  *)
(* just in case.                                                             *)
(* ------------------------------------------------------------------------- *)

let (LABEL_TAC: string -> thm_tactic) =
    fun s thm (asl,w) ->
        null_meta,[(s,thm)::asl,w],
        fun i [th] -> prove_asm_rule (INSTANTIATE_ALL i thm) th;;

let ASSUME_TAC = LABEL_TAC ""

(* ------------------------------------------------------------------------- *)
(* Manipulation of assumption list.                                          *)
(* ------------------------------------------------------------------------- *)

let (FIND_ASSUM: thm_tactic -> term -> tactic) =
    fun ttac t ((asl,w) as g) ->
        ttac(snd(find (fun (_,th) -> concl th = t) asl)) g

let (POP_ASSUM: thm_tactic -> tactic) =
    fun ttac ->
        function gl -> match gl with
                        | (((_,th)::asl),w)  -> ttac th (asl,w)
                        | _ -> failwith "POP_ASSUM: No assumption to pop"

let (ASSUM_LIST: (thm list -> tactic) -> tactic) =
    fun aslfun (asl,w) -> aslfun (map snd asl) (asl,w)

let (POP_ASSUM_LIST: (thm list -> tactic) -> tactic) =
    fun asltac (asl,w) -> asltac (map snd asl) ([],w)

let (EVERY_ASSUM: thm_tactic -> tactic) =
    fun ttac -> ASSUM_LIST (MAP_EVERY ttac)

let (FIRST_ASSUM: thm_tactic -> tactic) =
    fun ttac (asl,w as g) -> tryfind (fun (_,th) -> ttac th g) asl

/// Maps an inference rule over the assumptions of a goal.
let (RULE_ASSUM_TAC : (thm -> thm) -> tactic) = 
    fun rule (asl,w) ->
        (POP_ASSUM_LIST(arg1_fn ALL_TAC) 
         |> THEN <| MAP_EVERY (fun (s,th) -> LABEL_TAC s (rule th)) (rev asl)) (asl, w)

(* ------------------------------------------------------------------------- *)
(* Operate on assumption identified by a label.                              *)
(* ------------------------------------------------------------------------- *)

let (USE_THEN:string->thm_tactic->tactic) =
  fun s ttac (asl,w as gl) ->
    let th = try assoc s asl with Failure _ ->
             failwith("USE_TAC: didn't find assumption "^s) in
    ttac th gl

/// Returns position of given element in list.
// OPTIMIZE : Make this an alias for List.findIndex.
// Or, for more safety, modify this to return an option value, fix the call sites,
// then make this an alias for List.tryFindIndex.
let index x = 
    let rec ind n l = 
        match l with
        | [] -> failwith "index"
        | (h :: t) -> 
            if compare x h = 0 then n
            else ind (n + 1) t
    ind 0

let (REMOVE_THEN:string->thm_tactic->tactic) =
  fun s ttac (asl,w) ->
    let th = try assoc s asl with Failure _ ->
             failwith("USE_TAC: didn't find assumption " + s) in
    let asl1,asl2 = cut (index s (map fst asl)) asl in
    let asl' = asl1 @ tl asl2 in
    ttac th (asl',w)

(* ------------------------------------------------------------------------- *)
(* General tool to augment a required set of theorems with assumptions.      *)
(* ------------------------------------------------------------------------- *)

let (ASM :(thm list -> tactic)->(thm list -> tactic)) =
  fun tltac ths (asl,w as g) -> tltac (map snd asl @ ths) g

  (* ------------------------------------------------------------------------- *)
(* Basic tactic to use a theorem equal to the goal. Does *no* matching.      *)
(* ------------------------------------------------------------------------- *)

let (ACCEPT_TAC: thm_tactic) =
  let propagate_thm th i [] = INSTANTIATE_ALL i th in
  fun th (asl,w) ->
    if alpha_eq (concl th) w then
      null_meta,[],propagate_thm th
    else failwith "ACCEPT_TAC"

(* ------------------------------------------------------------------------- *)
(* Create tactic from a conversion. This allows the conversion to return     *)
(* |- p rather than |- p = T on a term "p". It also eliminates any goals of  *)
(* the form "T" automatically.                                               *)
(* ------------------------------------------------------------------------- *)

let (CONV_TAC: conv -> tactic) =
  let t_tm = parse_term @"true" in
  fun conv ((asl,w) as g) ->
    let th = conv w in
    let tm = concl th in
    if alpha_eq tm w then ACCEPT_TAC th g else
    let l,r = dest_eq tm in
    if not(alpha_eq l w) then failwith "CONV_TAC: bad equation" else
    if r = t_tm then ACCEPT_TAC(eqt_elim_rule th) g else
    let th' = sym_rule th in
    null_meta,[asl,r],fun i [th] -> prim_eq_mp_rule (INSTANTIATE_ALL i th') th

(* ------------------------------------------------------------------------- *)
(* Tactics for equality reasoning.                                           *)
(* ------------------------------------------------------------------------- *)

let (REFL_TAC: tactic) =
  fun ((asl,w) as g) ->
    try ACCEPT_TAC(prim_refl_conv(rand w)) g
    with Failure _ -> failwith "REFL_TAC"

(* ------------------------------------------------------------------------- *)
(* Convert a tactic into a refinement on head subgoal in current state.      *)
(* ------------------------------------------------------------------------- *)

let (by:tactic->refinement) =
  fun tac ((mvs,inst),gls,just) ->
    if gls = [] then failwith "No goal set" else
    let g = hd gls
    let ogls = tl gls in
    let ((newmvs,newinst),subgls,subjust) = tac g in
    let n = length subgls in
    let mvs' = union newmvs mvs
    let inst' = compose_insts inst newinst
    let gls' = subgls @ map (inst_goal newinst) ogls in
    let just' i ths =
      let i' = compose_insts inst' i in
      let cths,oths = cut n ths in
      let sths = (subjust i cths) :: oths in
      just i' sths in
    (mvs',inst'),gls',just'

(* ------------------------------------------------------------------------- *)
(* Rotate the goalstate either way.                                          *)
(* ------------------------------------------------------------------------- *)

let rec butlast l = 
    match l with
    | [_] -> []
    | (h :: t) -> h :: (butlast t)
    | [] -> failwith "butlast"

let (rotate:int->refinement) =
  let rotate_p (meta,sgs,just) =
    let sgs' = (tl sgs)@[hd sgs] in
    let just' i ths =
      let ths' = (last ths)::(butlast ths) in
      just i ths' in
    (meta,sgs',just')
  let rotate_n (meta,sgs,just) =
    let sgs' = (last sgs)::(butlast sgs) in
    let just' i ths =
      let ths' = (tl ths)@[hd ths] in
      just i ths' in
    (meta,sgs',just') in
  fun n -> if n > 0 then funpow n rotate_p
           else funpow (-n) rotate_n

(* ------------------------------------------------------------------------- *)
(* Perform refinement proof, tactic proof etc.                               *)
(* ------------------------------------------------------------------------- *)

let (mk_goalstate:goal->goalstate) =
  fun (asl,w) ->
    if type_of w = bool_ty then
      null_meta,[asl,w],
      (fun inst [th] -> INSTANTIATE_ALL inst th)
    else failwith "mk_goalstate: Non-boolean goal"

let (TAC_PROOF : goal * tactic -> thm) =
  fun (g,tac) ->
    let gstate = mk_goalstate g in
    let _,sgs,just = by tac gstate in
    if sgs = [] then just null_inst []
    else failwith "TAC_PROOF: Unsolved goals"

let prove(t,tac) =
  let th = TAC_PROOF(([],t),tac) in
  let t' = concl th in
  if t' = t then th else
  try prim_eq_mp_rule (ALPHA t' t) th
  with Failure _ -> failwith "prove: justification generated wrong theorem"

(* ------------------------------------------------------------------------- *)
(* Interactive "subgoal package" stuff.                                      *)
(* ------------------------------------------------------------------------- *)

let current_goalstack = ref ([] :goalstack)

let (refine:refinement->goalstack) =
  fun r ->
    let l = !current_goalstack in
    match l with
    | [] -> failwith "No current goal"
    | _ -> 
        let h = hd l in
        let res = r h :: l in
        current_goalstack := res;
        !current_goalstack

let flush_goalstack() =
  let l = !current_goalstack in
  current_goalstack := [hd l]

//let e1 tac = refine(by(VALID tac))
let e2 tac = refine(by(tac))

let r n = refine(rotate n)

let set_goal(asl,w) =
  current_goalstack :=
    [mk_goalstate(map (fun t -> "",assume_rule t) asl,w)];
  !current_goalstack

let rec sort cmp lis = 
    match lis with
    | [] -> []
    | piv :: rest -> 
        let r, l = partition (cmp piv) rest
        (sort cmp l) @ (piv :: (sort cmp r))

let g t =
  let fvs = sort (<) (map (fst << dest_var) (free_vars t)) in
  (if fvs <> [] then
     let errmsg = List.reduceBack (fun s t -> s^", "^t) fvs in
     warn true ("Free variables in goal: "^errmsg)
   else ());
   set_goal([],t)

let b() =
  let l = !current_goalstack in
  if length l = 1 then failwith "Can't back up any more" else
  current_goalstack := tl l;
  !current_goalstack

let p() =
  !current_goalstack

let top_realgoal() =
  let (_,((asl,w)::_),_)::_ = !current_goalstack in
  asl,w

let top_goal() =
  let asl,w = top_realgoal() in
  map (concl << snd) asl,w

let top_thm() =
  let (_,[],f)::_ = !current_goalstack in
  f null_inst []
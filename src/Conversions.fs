// experiment porting from hol_light

[<AutoOpen>]
module HOL.Conversions

(* ------------------------------------------------------------------------- *)
(* Type abbreviation for conversions.                                        *)
(* ------------------------------------------------------------------------- *)

type conv = term -> thm

(* ------------------------------------------------------------------------- *)
(* A bit more syntax.                                                        *)
(* ------------------------------------------------------------------------- *)

/// Take left-hand argument of a binary operator.
let lhand = rand << rator
/// Returns the left-hand side of an equation.
let lhs = fst << dest_eq
/// Returns the right-hand side of an equation.
let rhs = snd << dest_eq

(* ------------------------------------------------------------------------- *)
(* Similar to variant, but even avoids constants, and ignores types.         *)
(* ------------------------------------------------------------------------- *)

/// Rename variable to avoid specified names and constant names.
let mk_primed_var = cvariant

(* ------------------------------------------------------------------------- *)
(* General case of beta-conversion.                                          *)
(* ------------------------------------------------------------------------- *)

/// Returns the bound variable of an abstraction.
let bndvar tm = 
    try 
        fst(dest_abs tm)
    with
    | Failure _ -> hol_fail("bndvar","Not an abstraction")

/// General case of beta-conversion.
//let BETA_CONV tm = 
//    try 
//        beta_conv tm
//    with
//    | Failure _ -> 
//        try 
//            let f, arg = dest_comb tm
//            let v = bndvar f
//            inst_rule [arg, v] (beta_conv(mk_comb(f, v)))
//        with
//        | Failure _ -> hol_fail("BETA_CONV","Not a beta-redex")

(* ------------------------------------------------------------------------- *)
(* A few very basic derived equality rules.                                  *)
(* ------------------------------------------------------------------------- *)

// Queste sono regole derivate copiate da equal.fs. Sarebbe meglio prima vedere che hol_zero non le abbia già
// iniziare mettendo il commento su quello che fanno così come c'è per le altre regole definite in hol_zero

///// Applies a function to both sides of an equational theorem.
//let mk_comb2_rule (tm:term) th =
//    try prim_mk_comb_rule (prim_refl_conv tm) th
//    with Failure _ -> failwith "mk_comb2_rule"

///// Proves equality of equal functions applied to a term.
//let mk_comb1_rule th tm =
//    try prim_mk_comb_rule th (prim_refl_conv tm)
//    with Failure _ -> failwith "mk_comb1_rule"

///// Swaps left-hand and right-hand sides of an equation.
//let sym_rule th =
//    let tm = concl th in
//    let l,r = dest_eq tm in
//    let lth = prim_refl_conv l in
//    prim_eq_mp_rule (prim_mk_comb_rule (mk_comb2_rule (rator (rator tm)) th) lth) lth

/// Proves equality of lpha-equivalent terms.
let ALPHA tm1 tm2 =
    try trans_rule (prim_refl_conv tm1) (prim_refl_conv tm2)
    with Failure _ -> failwith "ALPHA"

(* ------------------------------------------------------------------------- *)
(* Alpha conversion term operation.                                          *)
(* ------------------------------------------------------------------------- *)

/// Changes the name of a bound variable.
let alpha v tm =
    let v0,bod = try dest_abs tm
                 with Failure _ -> failwith "alpha: Not an abstraction"in
    if v = v0 then tm else
    if type_of v = type_of v0 && not (var_free_in v bod) then
      mk_abs(v,vsubst[v,v0]bod)
    else failwith "alpha: Invalid new variable"

/// Renames the bound variable of a lambda-abstraction.
let ALPHA_CONV v tm =
    let res = alpha v tm
    ALPHA tm res

/// Renames the bound variable of an abstraction or binder.
let GEN_ALPHA_CONV v tm =
    if is_abs tm then ALPHA_CONV v tm else
    let b,abs = dest_comb tm in
    mk_comb2_rule b (ALPHA_CONV v abs)

/// Compose equational theorems with binary operator.
let MK_BINOP op (lth,rth) =
    prim_mk_comb_rule (mk_comb2_rule op lth) (rth)

(* ------------------------------------------------------------------------- *)
(* Terminal conversion combinators.                                          *)
(* ------------------------------------------------------------------------- *)

let (NO_CONV:conv) = fun tm -> failwith "NO_CONV"

let (ALL_CONV:conv) = prim_refl_conv

(* ------------------------------------------------------------------------- *)
(* Combinators for sequencing, trying, repeating etc. conversions.           *)
(* ------------------------------------------------------------------------- *)

/// Applies two conversions in sequence.
let THENC : conv -> conv -> conv =
  fun conv1 conv2 t ->
    let th1 = conv1 t in
    let th2 = conv2 (rand(concl th1)) in
    trans_rule th1 th2

/// Applies the first of two conversions that succeeds.
let ORELSEC : conv -> conv -> conv =
    fun conv1 conv2 t ->
        try conv1 t with Failure _ -> conv2 t

/// Apply the first of the conversions in a given list that succeeds.
let (FIRST_CONV:conv list -> conv) = List.reduceBack (fun c1 c2 -> c1 |> ORELSEC <| c2)

/// Applies in sequence all the conversions in a given list of conversions.
let (EVERY_CONV:conv list -> conv) =
    fun l -> List.foldBack (fun c1 c2 -> c1 |> THENC <| c2) l ALL_CONV

/// Repeatedly apply a conversion (zero or more times) until it fails.
let REPEATC =
    let rec REPEATC conv t =
        ((conv |> THENC <| (REPEATC conv)) |> ORELSEC <| ALL_CONV) t
    (REPEATC:conv->conv)

/// Makes a conversion fail if applying it leaves a term unchanged.
let (CHANGED_CONV:conv->conv) =
    fun conv tm ->
        let th = conv tm in
        let l,r = dest_eq (concl th) in
        if alpha_eq l r then failwith "CHANGED_CONV" else th

/// Attempts to apply a conversion; applies identity conversion in case of failure.
let TRY_CONV conv = conv |> ORELSEC <| ALL_CONV

(* ------------------------------------------------------------------------- *)
(* Subterm conversions.                                                      *)
(* ------------------------------------------------------------------------- *)

/// Applies a conversion to the operator of an application.
let (RATOR_CONV:conv->conv) =
    fun conv tm ->
        let l,r = dest_comb tm in mk_comb1_rule (conv l) r

/// Applies a conversion to the operand of an application.
let (RAND_CONV:conv->conv) =
    fun conv tm ->
        let l,r = dest_comb tm in mk_comb2_rule l (conv r)

/// Apply a conversion to left-hand argument of binary operator.
let LAND_CONV = RATOR_CONV << RAND_CONV

/// Applies two conversions to the two sides of an application.
let (COMB2_CONV: conv->conv->conv) =
    fun lconv rconv tm -> 
        let l,r = dest_comb tm 
        prim_mk_comb_rule (lconv l) (rconv r)

/// Applies a conversion to the two sides of an application.
let COMB_CONV = dbl_arg COMB2_CONV

/// Applies a conversion to the body of an abstraction.
let (ABS_CONV:conv->conv) =
  fun conv tm ->
    let v,bod = dest_abs tm in
    let th = conv bod in
    try prim_mk_abs_rule v th with Failure _ ->
        let gv = genvar(type_of v) in
        let gbod = vsubst[gv,v] bod in
        let gth = prim_mk_abs_rule gv (conv gbod) in
        let gtm = concl gth in
        let l,r = dest_eq gtm in
        let v' = variant (free_vars gtm) v in
        let l' = alpha v' l 
        let r' = alpha v' r
        prim_eq_mp_rule (ALPHA gtm (mk_eq(l',r'))) gth

/// Applies conversion to the body of a binder.
let BINDER_CONV conv tm =
    if is_abs tm then ABS_CONV conv tm
    else RAND_CONV(ABS_CONV conv) tm

/// Applies a conversion to the top-level subterms of a term.
let SUB_CONV conv tm =
    match tm with
    | Tmcomb(_,_) -> COMB_CONV conv tm
    | Tmabs(_,_) -> ABS_CONV conv tm
    | _ -> prim_refl_conv tm

/// Applies a conversion to both arguments of a binary operator.
let BINOP_CONV conv tm =
    let lop,r = dest_comb tm
    let op,l = dest_comb lop
    prim_mk_comb_rule (mk_comb2_rule op (conv l)) (conv r)

(* ------------------------------------------------------------------------- *)
(* Depth conversions; internal use of a failure-propagating 'Boultonized'    *)
(* version to avoid a great deal of rebuilding of terms.                     *)
(* ------------------------------------------------------------------------- *)

let THENQC conv1 conv2 tm =
    try let th1 = conv1 tm
        try let th2 = conv2(rand(concl th1)) in trans_rule th1 th2
        with Failure _ -> th1
    with Failure _ -> conv2 tm

let THENCQC conv1 conv2 tm =
    let th1 = conv1 tm in
    try let th2 = conv2(rand(concl th1)) in trans_rule th1 th2
    with Failure _ -> th1

let COMB_QCONV conv tm =
    let l,r = dest_comb tm in
    try let th1 = conv l in
        try let th2 = conv r in prim_mk_comb_rule th1 th2
        with Failure _ -> mk_comb1_rule th1 r
    with Failure _ -> mk_comb2_rule l (conv r)

let rec REPEATQC conv tm = THENCQC conv (REPEATQC conv) tm

let SUB_QCONV conv tm =
    if is_abs tm then ABS_CONV conv tm
    else COMB_QCONV conv tm

let rec ONCE_DEPTH_QCONV conv tm =
    (conv |> ORELSEC <| (SUB_QCONV (ONCE_DEPTH_QCONV conv))) tm

let rec DEPTH_QCONV conv tm =
    THENQC (SUB_QCONV (DEPTH_QCONV conv))
           (REPEATQC conv) tm

let rec REDEPTH_QCONV conv tm =
    THENQC (SUB_QCONV (REDEPTH_QCONV conv))
           (THENCQC conv (REDEPTH_QCONV conv)) tm

let rec TOP_DEPTH_QCONV conv tm =
    THENQC (REPEATQC conv)
           (THENCQC (SUB_QCONV (TOP_DEPTH_QCONV conv))
                    (THENCQC conv (TOP_DEPTH_QCONV conv))) tm

let rec TOP_SWEEP_QCONV conv tm =
    THENQC (REPEATQC conv)
           (SUB_QCONV (TOP_SWEEP_QCONV conv)) tm

/// Applies a conversion once to the first suitable sub-term(s) encountered in top-down order.
let ONCE_DEPTH_CONV (c : conv) : conv = TRY_CONV (ONCE_DEPTH_QCONV c)

/// Applies a conversion repeatedly to all the sub-terms of a term, in bottom-up order.
let DEPTH_CONV (c : conv) : conv = TRY_CONV (DEPTH_QCONV c)

/// Applies a conversion bottom-up to all subterms, retraversing changed ones.
let REDEPTH_CONV (c : conv) : conv = TRY_CONV (REDEPTH_QCONV c)

/// Applies a conversion top-down to all subterms, retraversing changed ones.
let TOP_DEPTH_CONV (c : conv) : conv = TRY_CONV (TOP_DEPTH_QCONV c)

/// Repeatedly applies a conversion top-down at all levels,
/// but after descending to subterms, does not return to higher ones.
let TOP_SWEEP_CONV (c : conv) : conv = TRY_CONV (TOP_SWEEP_QCONV c)

(* ------------------------------------------------------------------------- *)
(* Apply at leaves of op-tree; NB any failures at leaves cause failure.      *)
(* ------------------------------------------------------------------------- *)

/// Breaks apart an application of a given binary operator to two arguments.
// from basics
let dest_binop op tm =
    match tm with
    | Tmcomb(Tmcomb(op',l),r) when op' = op -> (l,r)
    | _ -> failwith "dest_binop"

/// Applied a conversion to the leaves of a tree of binary operator expressions.
let rec DEPTH_BINOP_CONV op conv tm =
    match tm with
      Tmcomb(Tmcomb(op',l),r) when op' = op ->
        let l,r = dest_binop op tm in
        let lth = DEPTH_BINOP_CONV op conv l
        let rth = DEPTH_BINOP_CONV op conv r
        prim_mk_comb_rule(mk_comb2_rule op' lth) (rth)
    | _ -> conv tm

(* ------------------------------------------------------------------------- *)
(* Follow a path.                                                            *)
(* ------------------------------------------------------------------------- *)

/// Follow a path.
let PATH_CONV =
    let rec path_conv s cnv =
      match s with
      | [] -> cnv
      | "l"::t -> RATOR_CONV (path_conv t cnv)
      | "r"::t -> RAND_CONV (path_conv t cnv)
      | _::t -> ABS_CONV (path_conv t cnv) in
    fun s cnv -> path_conv (explode s) cnv

(* ------------------------------------------------------------------------- *)
(* Follow a pattern                                                          *)
(* ------------------------------------------------------------------------- *)

/// Follow a pattern.
let PAT_CONV =
    let rec PCONV xs pat conv =
        if mem pat xs then conv
        else if not(exists (fun x -> var_free_in x pat) xs) then ALL_CONV
        else if is_comb pat then
            COMB2_CONV (PCONV xs (rator pat) conv) (PCONV xs (rand pat) conv)
        else
            ABS_CONV (PCONV xs (body pat) conv) in
    fun pat -> let xs,pbod = strip_abs pat in PCONV xs pbod

(* ------------------------------------------------------------------------- *)
(* sym_rulemetry conversion.                                                      *)
(* ------------------------------------------------------------------------- *)

/// sym_rulemetry conversion.
let sym_rule_CONV tm =
    try let th1 = sym_rule(assume_rule tm) in
        let tm' = concl th1 in
        let th2 = sym_rule(assume_rule tm') in
        deduct_antisym_rule th2 th1
    with Failure _ -> failwith "sym_rule_CONV"

(* ------------------------------------------------------------------------- *)
(* Conversion to a rule.                                                     *)
(* ------------------------------------------------------------------------- *)

let CONV_RULE (conv:conv) th =
    prim_eq_mp_rule (conv(concl th)) th

(* ------------------------------------------------------------------------- *)
(* Substitution conversion.                                                  *)
(* ------------------------------------------------------------------------- *)

/// Substitution conversion.
let SUBS_CONV ths tm =
  try if ths = [] then prim_refl_conv tm else
      let lefts = map (lhand << concl) ths in
      let gvs = map (genvar << type_of) lefts in
      let pat = subst (zip gvs lefts) tm in
      let abs = list_mk_abs(gvs,pat) in
      let th = List.fold
                (fun y x -> CONV_RULE (RAND_CONV beta_conv |> THENC <| LAND_CONV beta_conv)
                                      (prim_mk_comb_rule x y)) (prim_refl_conv abs) ths in
      if rand(concl th) = tm then prim_refl_conv tm else th
  with Failure _ -> failwith "SUBS_CONV"

(* ------------------------------------------------------------------------- *)
(* Get a few rules.                                                          *)
(* ------------------------------------------------------------------------- *)

let BETA_RULE = CONV_RULE(REDEPTH_CONV beta_conv)

let Gsym_rule = CONV_RULE(ONCE_DEPTH_CONV sym_rule_CONV)

let SUBS ths = CONV_RULE (SUBS_CONV ths)

(* ------------------------------------------------------------------------- *)
(* A cacher for conversions.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t

let CACHE_CONV =
  let ALPHA_HACK th =
    let tm' = lhand(concl th) in
    fun tm -> if tm' = tm then th else trans_rule (ALPHA tm tm') th in
  fun conv ->
    let net = ref empty_net in
    fun tm -> try tryfind (fun f -> f tm) (lookup tm (!net))
              with Failure _ ->
                  let th : thm = conv tm in
                  net := enter [] (tm,ALPHA_HACK th) (!net)
                  th

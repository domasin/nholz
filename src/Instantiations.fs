// experiment porting from hol_light

[<AutoOpen>]
module HOL.Instantiations

(* ------------------------------------------------------------------------- *)
(* Type of instantiations, with terms, types and higher-order data.          *)
(* ------------------------------------------------------------------------- *)

type instantiation =
    (int * term) list * (term * term) list * (hol_type * hol_type) list

(* ------------------------------------------------------------------------- *)
(* The last recourse when all else fails!                                    *)
(* ------------------------------------------------------------------------- *)

/// Creates an arbitrary theorem as an axiom (dangerous!)
let mk_thm(asl,c) =
      let ax = new_axiom("", List.foldBack (curry mk_imp) (rev asl) c) in
      List.fold (fun th t -> prim_mp_rule th (assume_rule t)) ax (rev asl) 

(* ------------------------------------------------------------------------- *)
(* Eliminate the antecedent of a theorem using a conversion/proof rule.      *)
(* ------------------------------------------------------------------------- *)

/// Removes antecedent of implication theorem by solving it with a conversion.
let MP_CONV (cnv:conv) th =
    let l,r = dest_imp(concl th) in
    let ath = cnv l in
    try prim_mp_rule th (eqt_elim_rule ath) with Failure _ -> prim_mp_rule th ath

(* ------------------------------------------------------------------------- *)
(* Multiple beta-reduction (we use a slight variant below).                  *)
(* ------------------------------------------------------------------------- *)

/// Beta conversion over multiple arguments.
let rec BETAS_CONV tm =
    match tm with
    | Tmcomb(Tmabs(_,_),_) -> beta_conv tm
    | Tmcomb(Tmcomb(_,_),_) -> ((RATOR_CONV BETAS_CONV) |> THENC <| beta_conv) tm
    | _ -> failwith "BETAS_CONV"

/// Applies a binary function between adjacent elements of the reverse of a list.
// From Lib
let rec rev_itlist f l b = 
    match l with
    | [] -> b
    | (h :: t) -> rev_itlist f t (f h b)

/// Searches a list of pairs for a pair whose second component equals a specified value.
// From Lib
let rec rev_assoc a l = 
    match l with
    | (x, y) :: t -> 
        if compare y a = 0 then x
        else rev_assoc a t
    | [] -> failwith "find"

(* ------------------------------------------------------------------------- *)
(* Instantiators.                                                            *)
(* ------------------------------------------------------------------------- *)
/// Apply a higher-order instantiation to a term.
let (instantiate : instantiation -> term -> term) = 
    let betas n tm = 
        let args, lam = funpow n (fun (l, t) -> (rand t) :: l, rator t) ([], tm)
        rev_itlist (fun a l -> 
                let v, b = dest_abs l
                vsubst [a, v] b) args lam
    let rec ho_betas bcs pat tm = 
        if is_var pat || is_const pat
        then hol_fail ("","")
        else 
            try 
                let bv, bod = dest_abs tm
                mk_abs(bv, ho_betas bcs (body pat) bod)
            with
            | Failure _ -> 
                let hop, args = strip_comb pat
                try 
                    let n = rev_assoc hop bcs
                    if length args = n
                    then betas n tm
                    else hol_fail ("","")
                with
                | Failure _ -> 
                    let lpat, rpat = dest_comb pat
                    let ltm, rtm = dest_comb tm
                    try 
                        let lth = ho_betas bcs lpat ltm
                        try 
                            let rth = ho_betas bcs rpat rtm
                            mk_comb(lth, rth)
                        with
                        | Failure _ -> mk_comb(lth, rtm)
                    with
                    | Failure _ -> 
                        let rth = ho_betas bcs rpat rtm
                        mk_comb(ltm, rth)
    fun (bcs, tmin, tyin) tm -> 
        let itm = 
            if tyin = []
            then tm
            else tyvar_inst tyin tm
        if tmin = []
        then itm
        else 
            let ttm = vsubst tmin itm
            if bcs = []
            then ttm
            else 
                try 
                    ho_betas bcs itm ttm
                with
                | Failure _ -> ttm

let (INSTANTIATE : instantiation->thm->thm) =
  let rec BETAS_CONV n tm =
    if n = 1 then TRY_CONV beta_conv tm else
    (RATOR_CONV (BETAS_CONV (n-1)) |> THENC <| 
     TRY_CONV beta_conv) tm in
  let rec HO_BETAS bcs pat tm =
    if is_var pat || is_const pat then failwith "INSTANTIATE" else
    try let bv,bod = dest_abs tm in
        prim_mk_abs_rule bv (HO_BETAS bcs (body pat) bod)
    with Failure _ ->
        let hop,args = strip_comb pat in
        try let n = rev_assoc hop bcs in
            if length args = n then BETAS_CONV n tm else failwith "INSTANTIATE"
        with Failure _ ->
            let lpat,rpat = dest_comb pat in
            let ltm,rtm = dest_comb tm in
            try let lth = HO_BETAS bcs lpat ltm in
                try let rth = HO_BETAS bcs rpat rtm in
                    prim_mk_comb_rule lth rth
                with Failure _ ->
                    mk_comb1_rule lth rtm
            with Failure _ ->
                let rth = HO_BETAS bcs rpat rtm in
                mk_comb2_rule ltm rth in
  fun (bcs,tmin,tyin) th ->
    let ith = if tyin = [] then th else prim_inst_type_rule tyin th in
    if tmin = [] then ith else
    let tth = prim_inst_rule tmin ith in
    if asms tth = asms th then
      if bcs = [] then tth else
      try let eth = HO_BETAS bcs (concl ith) (concl tth) in
          prim_eq_mp_rule eth tth
      with Failure _ -> tth
    else failwith "INSTANTIATE: term or type var free in assumptions"

let (INSTANTIATE_ALL : instantiation->thm->thm) =
  fun ((_,tmin,tyin) as i) th ->
    if tmin = [] && tyin = [] then th else
    let hyps = asms th in
    if hyps = [] then INSTANTIATE i th else
    let tyrel,tyiirel =
      if tyin = [] then [],hyps else
      let tvs = List.foldBack (union << type_tyvars << snd) tyin [] in
      partition (fun tm -> let tvs' = term_tyvars tm in
                           not(intersect tvs tvs' = [])) hyps in
    let tmrel,tmirrel =
      if tmin = [] then [],tyiirel else
      let vs = List.foldBack (union << free_vars << snd) tmin [] in
      partition (fun tm -> let vs' = free_vars tm in
                           not (intersect vs vs' = [])) tyiirel in
    let rhyps = union tyrel tmrel in
    let th1 = rev_itlist prim_disch_rule rhyps th in
    let th2 = INSTANTIATE i th1 in
    funpow (length rhyps) undisch_rule th2

(* ------------------------------------------------------------------------- *)
(* Higher order matching of terms.                                           *)
(*                                                                           *)
(* Note: in the event of spillover patterns, this may return false results;  *)
(* but there's usually an implicit check outside that the match worked       *)
(* anyway. A test could be put in (see if any "env" variables are left in    *)
(* the term after abstracting out the pattern instances) but it'd be slower. *)
(* ------------------------------------------------------------------------- *)

/// The type variable ':A'.
let aty = Tyvar "A"

/// Prints out a warning string.
let warn cond s =
    if cond then
        report("Warning: " + s)

let rec mapfilter f l =
  match l with
    [] -> []
  | (h::t) -> let rest = mapfilter f t in
              try (f h)::rest with Failure _ -> rest

let (term_match_hl:term list -> term -> term -> instantiation) =
  let safe_inserta ((y,x) as n) l =
    try let z = rev_assoc x l in
        if alpha_eq y z then l else failwith "safe_inserta"
    with Failure "find" -> n::l in

  let safe_insert ((y,x) as n) l =
    try let z = rev_assoc x l in
        if compare y z = 0 then l else failwith "safe_insert"
    with Failure "find" -> n::l in

  let mk_dummy =
    let name = fst(dest_var(genvar aty)) in
    fun ty -> mk_var(name,ty) in

  let rec term_pmatch lconsts env vtm ctm ((insts,homs) as sofar) =
    match (vtm,ctm) with
      Tmvar(_,_),_ ->
       (try let ctm' = rev_assoc vtm env in
            if compare ctm' ctm = 0 then sofar 
            else failwith "term_pmatch"
        with Failure "find" ->
            if mem vtm lconsts then
              if compare ctm vtm = 0 then sofar
              else failwith "term_pmatch: can't instantiate local constant"
            else safe_inserta (ctm,vtm) insts,homs)
    | Tmconst(vname,vty),Tmconst(cname,cty) ->
        if compare vname cname = 0 then
          if compare vty cty = 0 then sofar
          else safe_insert (mk_dummy cty,mk_dummy vty) insts,homs
        else failwith "term_pmatch"
    | Tmabs(vv,vbod),Tmabs(cv,cbod) ->
        let sofar' = safe_insert (mk_dummy(snd(dest_var cv)),mk_dummy(snd(dest_var vv))) insts,homs
        term_pmatch lconsts ((cv,vv)::env) vbod cbod sofar'
    | _ ->
      let vhop = repeat rator vtm in
      if is_var vhop & not (mem vhop lconsts) &
                       not (can (rev_assoc vhop) env) then
        let vty = type_of vtm 
        let cty = type_of ctm in
        let insts' =
          if compare vty cty = 0 then insts
          else safe_insert (mk_dummy cty,mk_dummy vty) insts in
        (insts',(env,ctm,vtm)::homs)
      else
        let lv,rv = dest_comb vtm
        let lc,rc = dest_comb ctm in
        let sofar' = term_pmatch lconsts env lv lc sofar in
        term_pmatch lconsts env rv rc sofar' in

  let get_type_insts insts acc =
        (insts, acc)
        ||> List.foldBack 
            (
                fun (t, x) sofar ->
                let dest_var_x = dest_var x
                let type_of_t = type_of t
                type_match0 sofar (snd dest_var_x) type_of_t
            )

  let separate_insts insts =
      let realinsts,patterns = partition (is_var << snd) insts in
      let betacounts =
        if patterns = [] then [] 
        else
            List.foldBack 
              (fun (_,p) sof ->
                let hop,args = strip_comb p in
                try safe_insert (length args,hop) sof with Failure _ ->
                (warn true "Inconsistent patterning in higher order match"; sof))
              patterns [] in
      let tyins = get_type_insts realinsts [] in
      betacounts,
      mapfilter (fun (t,x) ->
        let x' = let xn,xty = dest_var x in
                 mk_var(xn,type_inst tyins xty) in
        if compare t x' = 0 then failwith "separate_insts" else (t,x')) realinsts,
      tyins in

  let rec term_homatch lconsts tyins (insts,homs) =
    if homs = [] then insts else
    let (env,ctm,vtm) = hd homs in
    if is_var vtm then
      if compare ctm vtm = 0 then term_homatch lconsts tyins (insts,tl homs) 
      else
          let newtyins = safe_insert (type_of ctm,snd(dest_var vtm)) tyins
          let newinsts = (ctm,vtm)::insts in
          term_homatch lconsts newtyins (newinsts,tl homs) 
    else
        let vhop,vargs = strip_comb vtm in
        let afvs = list_free_vars vargs in
        let inst_fn = tyvar_inst tyins in
        try 
            let tmins = map
                              (fun a -> (try rev_assoc a env with Failure _ -> 
                                            try
                                                rev_assoc a insts 
                                            with Failure _ ->
                                             if mem a lconsts then a else failwith "term_homatchs"
                                        ), inst_fn a) afvs in
            let pats0 = map inst_fn vargs in
            let pats = map (vsubst tmins) pats0 in
            let vhop' = inst_fn vhop in
            let ni =
              let chop,cargs = strip_comb ctm in
              if compare cargs pats = 0 then
                if compare chop vhop = 0 then insts else safe_inserta (chop,vhop) insts 
              else
                  let ginsts = map (fun p -> (if is_var p then p else genvar(type_of p)),p) pats in
                  let ctm' = subst ginsts ctm
                  let gvs = map fst ginsts in
                  let abstm = list_mk_abs(gvs,ctm') in
                  let vinsts = safe_inserta (abstm,vhop) insts in
                  let icpair = ctm',list_mk_comb(vhop',gvs) in
                  icpair::vinsts in
            term_homatch lconsts tyins (ni,tl homs)
        with Failure _ ->
            let lc,rc = dest_comb ctm
            let lv,rv = dest_comb vtm in
            let pinsts_homs' =
              term_pmatch lconsts env rv rc (insts,(env,lc,lv)::(tl homs)) in
            let tyins' = get_type_insts (fst pinsts_homs') [] in
            term_homatch lconsts tyins' pinsts_homs' in

  fun lconsts vtm ctm ->
    let pinsts_homs = term_pmatch lconsts [] vtm ctm ([],[]) in
    let tyins = get_type_insts (fst pinsts_homs) [] in
    let insts = term_homatch lconsts tyins pinsts_homs in
    separate_insts insts

(* ------------------------------------------------------------------------- *)
(* First order unification (no type instantiation -- yet).                   *)
(* ------------------------------------------------------------------------- *)

let (term_unify:term list -> term -> term -> instantiation) =
  let augment1 sofar (s,x) =
    let s' = subst sofar s in
    if var_free_in x s && not (s = x) then failwith "augment_insts"
    else (s',x) in
  let raw_augment_insts p insts =
    p::(map (augment1 [p]) insts) in
  let augment_insts(t,v) insts =
    let t' = vsubst insts t in
    if t' = v then insts
    else if var_free_in v t' then failwith "augment_insts"
    else raw_augment_insts (t',v) insts in
  let rec unify vars tm1 tm2 sofar =
    if tm1 = tm2 then sofar
    else if is_var tm1 && mem tm1 vars then
      try let tm1' = rev_assoc tm1 sofar in
          unify vars tm1' tm2 sofar
      with Failure "find" ->
          augment_insts (tm2,tm1) sofar
    else if is_var tm2 & mem tm2 vars then
       try 
            let tm2' = rev_assoc tm2 sofar in
            unify vars tm1 tm2' sofar
       with Failure "find" ->
          augment_insts (tm1,tm2) sofar
    else if is_abs tm1 then
      let tm1' = body tm1
      let tm2' = subst [bndvar tm1,bndvar tm2] (body tm2) in
      unify vars tm1' tm2' sofar
    else
      let l1,r1 = dest_comb tm1
      let l2,r2 = dest_comb tm2 in
      unify vars l1 l2 (unify vars r1 r2 sofar) in
  fun vars tm1 tm2 -> [],unify vars tm1 tm2 [],[]

(* ------------------------------------------------------------------------- *)
(* Modify bound variable names at depth. (Not very efficient...)             *)
(* ------------------------------------------------------------------------- *)

let deep_alpha =
  let tryalpha v tm =
    try alpha v tm
    with Failure _ -> 
        try
            let v' = variant (free_vars tm) v in
            alpha v' tm
        with Failure _ -> tm in
  let rec deep_alpha env tm =
    if env = [] then tm else
    try let v,bod = dest_abs tm in
        let vn,vty = dest_var v in
        try let (vn',_),newenv = remove1 (fun (_,x) -> x = vn) env in
            let v' = mk_var(vn',vty) in
            let tm' = tryalpha v' tm in
            let iv,ib = dest_abs tm' in
            mk_abs(iv,deep_alpha newenv ib)
        with Failure _ -> mk_abs(v,deep_alpha env bod)
    with Failure _ -> 
        try
            let l,r = dest_comb tm in
            mk_comb(deep_alpha env l,deep_alpha env r)
        with Failure _ -> tm in
  deep_alpha

(* ------------------------------------------------------------------------- *)
(* Instantiate theorem by matching part of it to a term.                     *)
(* The GEN_PART_MATCH version renames free vars to avoid clashes.            *)
(* ------------------------------------------------------------------------- *)

/// Generalizes zero or more variables in the conclusion of a theorem.
// from bool.fs
let GENL = List.foldBack gen_rule

let SPEC_VAR th =
  let bv = variant (thm_free_vars th) (bndvar(rand(concl th))) in
  bv,spec_rule bv th

let SPECL tms th =
  try rev_itlist spec_rule tms th
  with Failure _ -> failwith "SPECL"

let PART_MATCH,GEN_PART_MATCH =
  let rec match_bvs t1 t2 acc =
    try let v1,b1 = dest_abs t1
        let v2,b2 = dest_abs t2 in
        let n1 = fst(dest_var v1) 
        let n2 = fst(dest_var v2) in
        let newacc = if n1 = n2 then acc else insert (n1,n2) acc in
        match_bvs b1 b2 newacc
    with Failure _ -> 
        try
            let l1,r1 = dest_comb t1
            let l2,r2 = dest_comb t2 in
            match_bvs l1 l2 (match_bvs r1 r2 acc)
        with Failure _ -> acc in
  let PART_MATCH partfn th =
    let sth = spec_all_rule th in
    let bod = concl sth in
    let pbod = partfn bod in
    let lconsts = intersect (free_vars (concl th)) (list_free_vars(asms th)) in
    fun tm ->
      let bvms = match_bvs tm pbod [] in
      let abod = deep_alpha bvms bod in
      let ath = prim_eq_mp_rule (ALPHA bod abod) sth in
      let insts = term_match_hl lconsts (partfn abod) tm in
      let fth = INSTANTIATE insts ath in
      if asms fth <> asms ath then failwith "PART_MATCH: instantiated hyps" else
      let tm' = partfn (concl fth) in
      if compare tm' tm = 0 then fth else
      try SUBS[ALPHA tm' tm] fth
      with Failure _ -> failwith "PART_MATCH: Sanity check failure"
  let GEN_PART_MATCH partfn th =
    let sth = spec_all_rule th in
    let bod = concl sth in
    let pbod = partfn bod in
    let lconsts = intersect (free_vars (concl th)) (list_free_vars(asms th)) in
    let fvs = subtract (subtract (free_vars bod) (free_vars pbod)) lconsts in
    fun tm ->
      let bvms = match_bvs tm pbod [] in
      let abod = deep_alpha bvms bod in
      let ath = prim_eq_mp_rule (ALPHA bod abod) sth in
      let insts = term_match_hl lconsts (partfn abod) tm in
      let eth = INSTANTIATE insts (GENL fvs ath) in
      let fth = List.foldBack (fun v th -> snd(SPEC_VAR th)) fvs eth in
      if asms fth <> asms ath then failwith "PART_MATCH: instantiated hyps" else
      let tm' = partfn (concl fth) in
      if compare tm' tm = 0 then fth else
      try SUBS[ALPHA tm' tm] fth
      with Failure _ -> failwith "PART_MATCH: Sanity check failure" in
  PART_MATCH,GEN_PART_MATCH

(* ------------------------------------------------------------------------- *)
(* Matching modus ponens.                                                    *)
(* ------------------------------------------------------------------------- *)

let MATCH_MP ith =
  let sth =
    try let tm = concl ith in
        let avs,bod = strip_forall tm in
        let ant,con = dest_imp bod in
        let svs,pvs = partition (swap_arg var_free_in ant) avs in
        if pvs = [] then ith else
        let th1 = SPECL avs (assume_rule tm) in
        let th2 = GENL svs (prim_disch_rule ant (GENL pvs (undisch_rule th1))) in
        prim_mp_rule (prim_disch_rule tm th2) ith
    with Failure _ -> failwith "MATCH_MP: Not an implication" in
  let match_fun = PART_MATCH (fst << dest_imp) sth in
  fun th -> try prim_mp_rule (match_fun (concl th)) th
            with Failure _ -> failwith "MATCH_MP: No match"
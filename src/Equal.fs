(* ========================================================================== *)
(* EQUALITY (HOL Zero)                                                        *)
(* - Extra theory and derived rules for equality reasoning                    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2013                            *)
(* ========================================================================== *)

(* ========================================================================== *)
(* F# Porting                                                                 *)
(*                                                                            *)
(* by Domenico Masini 2013                                                    *)
(* http://github.com/domasin/nholz                                        *)
(* ========================================================================== *)

///This module adds more constants and inference rules for basic reasoning
///using equality.                                                                                                       
[<AutoOpen>]
module HOL.Equal


(* ** NEW CONSTANTS ** *)


(* Let definition *)

/// The internal constant for let-expressions is called "LET".  It has special
/// support in the parser/printer, so that the quotation                      
///    `let x1 = s1 and x2 = s2 in t`                                         
/// is parsed/printed for the internal term                                   
///    `LET (LET (\x1 x2. t) s1) s2`.                                         
///
/// |- LET = (\(f:'a->'b) x. f x) 
let let_def =
    new_const_definition (parse_term(@"LET = (\(f:'a->'b) (x:'a). f x)"))

(* Let syntax functions *)

let mk_let (vtms,tm0) =
    let () = assert1 (forall (uncurry same_types) vtms)
                         ("mk_let","Let decl var type not equal to value type")
    let (vs,tms) = unzip vtms
    let tm1 = try1 list_mk_abs (vs,tm0)
                         ("mk_let","Let decl item LHS not a variable")
    let mk_let0 (tm0,tm) =
       let (ty1,ty2) = dest_fun_type (type_of tm0)
       let l = mk_iconst ("LET", [(a_ty,ty1);(b_ty,ty2)])
       mk_bin (l,tm0,tm) in
    foldl' mk_let0 (tm1,tms)

let dest_let tm =
    try
        let (tm1,tms) = unfoldl (dest_cbin "LET") tm
        let () = assert0 (is_nonempty tms)     LocalFail
        let (vs,tm2) = strip_abs tm1
        let (vs1,vs2) = cut (length tms) vs
        let tm0 = list_mk_abs (vs2,tm2)
        let vtms = zip vs1 tms
        (vtms,tm0)
    with HolFail _ | LocalFail -> hol_fail ("dest_let","Not a let-expression")

let is_let tm = can dest_let tm

/// ONTO
///
/// |- ONTO = (\(f:'a->'b). !y. ?x. y = f x)
let onto_def =
    new_const_definition (parse_term(@"ONTO = (\(f:'a->'b). !y. ?x. y = f x)"))

(* ** DERIVED INFERENCE RULES ** *)


//  mk_comb1_rule : thm -> term -> thm                                      
//                                                                          
/// This is the equality congruence rule for function application functions.
/// It takes an equality theorem over functions and a term, and supplies the
/// term as the argument to each side of the theorem.  The type of the      
/// supplied term must be the same as the domain type of the functions.     
///                                                                         
///    A |- f1 = f2   `t`                                                   
///    ------------------                                                   
///     A |- f1 t = f2 t                                                    
///
/// See also: mk_comb2_rule, mk_comb_rule.
let mk_comb1_rule th tm =            (* A |- f1 = f2    t    *)
    try
        mk_comb_rule th (refl_conv tm)            (* A |- f1 t = f2 t     *)
    with HolFail _ ->
        let func = "mk_comb1_rule"
        let () = assert1 (is_eqthm th) (func,"Arg 1 not an equality theorem")
        let ty = type_of tm
        let (ty',_) = try1 (dest_fun_type <* type_of <* eqthm_lhs) th
                                     (func,"Arg 1 not a function equality theorem")
        let () = assert1 (type_eq ty ty')
                           (func,"Function domain type not equal to argument type")
        internal_err func

//  mk_comb2_rule : term -> thm -> thm                                        
//                                                                            
/// This is the equality congruence rule for function application arguments.  
/// It takes a function term and an equality theorem, and applies the function
/// to each side of the theorem.  The domain type of the supplied function    
/// must be the same as the type of the theorem LHS/RHS.                      
///                                                                           
///    `f`   A |- t1 = t2                                                     
///    ------------------                                                     
///     A |- f t1 = f t2                                                      
///
/// See also: mk_comb1_rule, mk_comb_rule.
let mk_comb2_rule tm th =          (* f    A |- t1 = t2    *)
    try
        mk_comb_rule (refl_conv tm) th            (* A |- f t1 = f t2     *)
    with HolFail _ ->
        let func = "mk_comb2_rule"
        let () = assert1 (is_eqthm th) (func,"Arg 2 not an equality theorem")
        let ty = type_of tm in
        let (ty',_) = try1 (dest_fun_type <* type_of) tm
                                            (func,"Arg 1 not a function term")
        let () = assert1 (type_eq ty ty')
                           (func,"Function domain type not equal to argument type")
        internal_err func

(* trans_rule : thm -> thm -> thm                                             *)
(*                                                                            *)
(* This is the transitivity rule for equality.  It takes two equality theorem *)
(* arguments, where the first theorem's RHS is the same (modulo alpha-        *)
(* equivalence) as the second theorem's LHS.  It returns a theorem stating    *)
(* that the first theorem's LHS equals the second theorem's RHS, under the    *)
(* unioned assumptions of the two theorems.                                   *)
(*                                                                            *)
(*    A1 |- t1 = t2    A2 |- t2 = t3                                          *)
(*    ------------------------------                                          *)
(*          A1 u A2 |- t1 = t3                                                *)

let trans_rule tha thb =        (* A1 |- t1 = t2    A2 |- t2 = t3  *)
    try
        let et1 = rator (concl tha)
        let th1 = mk_comb2_rule et1 thb          (* A1 |- t1 = t2 <=> t1 = t3  *)
        eq_mp_rule th1 tha                       (* A1 u A2 |- t1 = t3         *)
    with HolFail _ ->
        let func = "trans_rule"
        let () = assert1 (is_eqthm tha)     (func,"Arg 1 not an equality theorem")
        let () = assert1 (is_eqthm thb)     (func,"Arg 2 not an equality theorem")
        let tm2 = eqthm_rhs tha  
        let tm2' = eqthm_lhs thb
        let () = assert1 (same_types tm2 tm2')   (func,"Types not equal")
        let () = assert1 (alpha_eq tm2 tm2') (func,"1st theorem RHS and 2nd theorem LHS not alpha-equivalent")
        internal_err func

let list_trans_rule ths = foldl1 trans_rule ths

(* sym_rule : thm -> thm                                                      *)
(*                                                                            *)
(* This is the symmetry rule for equality.  It swaps the LHS with the RHS in  *)
(* the supplied equality theorem.                                             *)
(*                                                                            *)
(*    A |- t1 = t2                                                            *)
(*    ------------                                                            *)
(*    A |- t2 = t1                                                            *)

let sym_rule th =                   (* A |- t1 = t2    *)
    try
        let (e,tm1) = (dest_comb <* rator <* concl) th
        let th1 = refl_conv tm1                       (* |- t1 = t1                *)
        let th2 = mk_comb_rule (mk_comb2_rule e th) th1
                                                      (* A |- t1 = t1 <=> t2 = t1  *)
        eq_mp_rule th2 th1                            (* A |- t2 = t1              *)
    with HolFail _ ->
        let func = "sym_rule"
        let () = assert1 (is_eqthm th)      (func,"Not an equality theorem")
        internal_err func

// app_beta_rhs_rule : thm -> term -> thm                                     
//                                                                            
/// This rule is for expanding a function defined in terms of a lambda         
/// abstraction.  It takes an equality theorem and a term argument, where the  
/// theorem RHS is a lambda abstraction with a binding variable of the same    
/// type as the term argument.  It returns a theorem stating that the theorem  
/// argument's LHS applied to the term argument is equal to the beta reduction 
/// of the lambda abstraction applied to the term argument.                    
///                                                                            
///    A |- f = (\v. t)   `s`                                                  
///    ----------------------                                                  
///      A |- f s = t[s/v]                                                     
let app_beta_rhs_rule th0 z =          (* |- f = (\v. t)     *)
    try
        let th1 = mk_comb1_rule th0 z                 (* |- f s = (\v. t) s        *)
        let th2 = beta_conv (eqthm_rhs th1)           (* |- (\v. t) s = t[s/v]     *)
        trans_rule th1 th2                            (* |- f s = t[s/v]           *)
    with HolFail _ ->
        let func = "app_beta_rhs_rule"
        let () = assert1 (is_eqthm th0)     (func,"Arg 1 not an equality theorem")
        let ty = type_of z
        let (ty',_) = try1 (dest_fun_type <* type_of <* eqthm_lhs) th0
                                    (func,"Arg 1 not a function equality theorem")
        let () = assert1 (type_eq ty ty')
                             (func,"Function domain type not equal argument type")
        internal_err func

let list_app_beta_rhs_rule th0 zs = foldl app_beta_rhs_rule th0 zs

(* app_beta_rule : thm -> term -> thm                                         *)
(*                                                                            *)
(*    A |- (\v1. t1) = (\v2. t2)   `s`                                        *)
(*    --------------------------------                                        *)
(*       A |- t1[s/v1] = t2[s/v2]                                             *)

let app_beta_rule th0 tm =      (* A |- (\v1. t1) = (\v2. t2)    s  *)
    try
        let th1 = mk_comb1_rule th0 tm            (* A |- (\v1. t1) s = (\v2. t2) s *)
        let (tm2,tm3) = dest_eq (concl th1)
        let th2 = beta_conv tm2                   (* |- (\v1. t1) s = t1[s/v1]      *)
        let th3 = beta_conv tm3                   (* |- (\v2. t2) s = t2[s/v2]      *)
        list_trans_rule [sym_rule th2; th1; th3]  (* A |- t1[s/v1] = t2[s/v2]       *)
    with HolFail _ ->
        let func = "app_beta_rule" 
        let (tm1,tm2) = try1 dest_eqthm th0 (func,"Arg 1 not an equality theorem") 
        let v1 = try1 avar tm1         (func,"Arg 1 LHS not a lambda abstraction") 
        let () = assert1 (is_abs tm2)  (func,"Arg 1 RHS not a lambda abstraction") 
        let () = assert1 (same_types v1 tm)
                          (func,"Function domain type not equal to argument type") 
        internal_err func

let list_app_beta_rule th0 tms = foldl app_beta_rule th0 tms

// alpha_link_conv : term -> term -> thm                                      
//                                                                            
/// This is the alpha linking conversion.  It takes two alpha-equivalent terms 
/// and returns a theorem stating that the second is equal to the first, under 
/// no assumptions.  Fails if the supplied terms are not alpha-equivalent.     
///                                                                            
///    `t'`   `t`                                                              
///    ----------                                                              
///    |- t = t'                                                               
let alpha_link_conv tm' tm =       (* t'   t  *)
    try
        let th1 = refl_conv tm                   (* |- t = t       *)
        let th2 = refl_conv tm'                  (* |- t' = t'     *)
        trans_rule th1 th2                       (* |- t = t'      *)
    with HolFail _ ->
        let func = "alpha_link_conv"
        let () = assert1 (alpha_eq tm tm')      (func,"Args not alpha-equivalent")
        internal_err func

// alpha_conv : term -> term -> thm                                           
//                                                                            
/// This is the alpha renaming conversion.  It replaces the binding variable   
/// and all occurrences of it in the supplied lambda abstraction term (the 2nd 
/// argument) with the supplied variable (the 1st argument).  The supplied     
/// variable must have the same type as the original binding variable, and     
/// must not occur free in the original body.                                  
///                                                                            
///          `y`   `\x. t`                                                    
///    -------------------------                                              
///    |- (\x. t) = (\y. t[y/x])                                              
let alpha_conv u tm =
    let func = "alpha_conv"
    let () = assert1 (is_var u)                  (func,"Arg 1 not a variable")
    let (v,tm0) = try1 dest_abs tm     (func,"Arg 2 not a lambda abstraction")
    let () = assert1 (same_types u v)
                (func,"Var's type not equal to lambda binding var's type")
    let () = assert1 (not (var_free_in u tm))
                                       (func,"Var occurs free in lambda body")
    let tm' = mk_abs (u, var_inst [(v,u)] tm0)
    alpha_link_conv tm' tm

(* subs_conv : thm list -> term -> thm                                        *)
(*                                                                            *)
(* This is the basic substitution conversion.  It takes a list of equality    *)
(* theorems and a term, and transforms the term by performing a single        *)
(* parallel substitution of its free subterms according to the equality       *)
(* theorems.  All free occurrences of equality theorem LHSs in the term get   *)
(* replaced.  The resulting theorem has the unioned assumptions of all the    *)
(* supplied theorems (regardless of whether they apply to the supplied        *)
(* theorem).                                                                  *)
(*                                                                            *)
(* Binding variables in the resulting theorem's RHS are renamed as necessary  *)
(* to avoid variable capture.  Note that if one equality theorem's LHS occurs *)
(* free in another's, then the theorem with the larger LHS gets used in       *)
(* preference, and if two equality theorems have alpha-equivalent LHSs, then  *)
(* the earlier theorem in the list gets used in preference.  If no equality   *)
(* theorems apply, then the returned theorem's conclusion's RHS is the same   *)
(* as its LHS.                                                                *)
(*                                                                            *)
(*    A1 |- s1 = t1   A2 |- s2 = t2   ..   `t`                                *)
(*    ----------------------------------------                                *)
(*     A1 u A2 u .. |- t = t[t1/s1,t2/s2,..]                                  *)

let beta_thm_rule th0 th =    (* A1 |- (\u. s) = (\v. t)    A2 |- x = y  *)
    let th1 = mk_comb_rule th0 th        (* A1 u A2 |- (\u. s) x = (\v. t) y   *)
    let (tm2,tm3) = dest_eq (concl th1)
    let th2 = beta_conv tm2              (* |- (\u. s) x = s[x/u]              *)
    let th3 = beta_conv tm3              (* |- (\v. t) y = t[y/v]              *)
    list_trans_rule [sym_rule th2; th1; th3]    (* A1 u A2 |- s[x/u] = t[y/v]  *)

let list_beta_thm_rule th0 ths = foldl beta_thm_rule th0 ths

let subs_conv ths tm =      (* A1 |- s1 = t1   ..   An |- sn = tn    t    *)
    try
        let lhss = map eqthm_lhs ths
        let gvs = map (genvar <* type_of) lhss
        let theta = zip lhss gvs
        let tm0 = subst theta tm
        let tm1 = list_mk_abs (gvs,tm0)
        let th0 = refl_conv tm1         (* A |- (\g1 .. gn. t0) = (\g1 .. gn. t0)  *)
        list_beta_thm_rule th0 ths
                         (* A1 u .. u Am |- t[s1/g1,..,sn/gn] = t[t1/g1,..tn/gn]   *)
    with HolFail _ ->
        let func = "subs_conv"
        let () = assert1 (forall is_eqthm ths)
                                     (func, "Arg 1 item is not an equality thm")
        internal_err func

(* subs_rule : thm list -> thm -> thm                                         *)
(*                                                                            *)
(* This is the basic substitution rule.  It takes a list of equality theorems *)
(* and a theorem, and performs a single parallel substitution of free         *)
(* subterms in the theorem's conclusion according to the equality theorems.   *)
(* All free occurrences of equality theorem LHSs in the theorem get replaced. *)
(* The resulting theorem has the unioned assumptions of all the supplied      *)
(* theorems (regardless of whether they apply to the supplied theorem).       *)
(*                                                                            *)
(* Binding variables in the resulting theorem are renamed as necessary to     *)
(* avoid variable capture.  Note that if one equality theorem's LHS occurs    *)
(* free in another's, then the theorem with the larger LHS gets used in       *)
(* preference, and if two equality theorems have alpha-equivalent LHSs, then  *)
(* the earlier theorem in the list gets used in preference.  If no equality   *)
(* theorems apply, then the returned theorem's conclusion is the same as the  *)
(* input's.                                                                   *)
(*                                                                            *)
(*    A1 |- s1 = t1   A2 |- s2 = t2   ..    A |- t                            *)
(*    --------------------------------------------                            *)
(*         A1 u A2 u .. |- t[t1/s1,t2/s2,..]                                  *)

let subs_rule ths th =
    let th1 = try2 (subs_conv ths) (concl th)        "subs_rule"
    eq_mp_rule th1 th

(* subst_conv : (term * thm) list -> term -> term -> thm                      *)
(*                                                                            *)
(* This is the template substitution conversion.  It takes a substitution     *)
(* scheme (in the form of an association list and a template term) followed   *)
(* by a main term, and transforms the main term by performing a single        *)
(* parallel substitution of its free subterms, according to the substitution  *)
(* scheme.  The template term determines which free occurrences of equality   *)
(* theorem LHSs in the main term get replaced, and reflects the syntactic     *)
(* structure of the term, except having template variable atoms in place of   *)
(* subterms due for replacement.  The association list maps each template     *)
(* variable to an equality theorem, with equality theorem LHS for the main    *)
(* term's original subterm and RHS for the subterm that replaces it.  The     *)
(* resulting theorem has the unioned assumptions of all the supplied theorems *)
(* (regardless of whether they apply to the supplied template).               *)
(*                                                                            *)
(* Binding variables in the resulting theorem are renamed as necessary to     *)
(* avoid variable capture.  Note that if two entries appear in the            *)
(* association list for the same template variable, then the earlier entry    *)
(* gets used, and that entries for variables that don't appear in the         *)
(* template are ignored.  If no entries apply, then the returned theorem's    *)
(* conclusion's RHS is the same as its LHS.                                   *)
(*                                                                            *)
(*       `v1`           `v2`          ..                                      *)
(*    A1 |- s1 = t1   A2 |- s2 = t2   ..   `t`   `t[s1/v1,s2/v2,..]`          *)
(*    --------------------------------------------------------------          *)
(*        A1 u A2 u .. |- t[s1/v1,s2/v2,..] = t[t1/v1,t2/v2,..]               *)

let subst_conv vths tmp tm =
    let (vs,ths) = unzip vths
    try
        let tm1 = list_mk_abs (vs,tmp)
        let th0 = refl_conv tm1           (* A |- (\v1 .. vn. t) = (\v1 .. vn. t)  *)
        let th1 = list_beta_thm_rule th0 ths
        let () = assert0 (alpha_eq (eqthm_lhs th1) tm)     LocalFail
        th1
    with HolFail _ | LocalFail ->
        let func = "subst_conv"
        let () = assert1 (forall is_var vs)
                     (func,"Substitution list domain element not a variable")
        let () = assert1 (forall is_eqthm ths)
                     (func,"Substitution list range element not an equality thm")
        let () = assert1 (forall (fun (v,th) -> same_types v (eqthm_lhs th)) vths)
                     (func,"Substitution list domain/range types not equal")
        let theta = try1 (var_match tmp) tm
                     (func,"Main Arg does not match template")
        let (theta1,theta2) = partition (fun (v,tm) -> mem' term_eq v vs) theta
        let () = assert1 (forall (fun (v,tm) -> alpha_eq (eqthm_lhs(assoc v vths)) tm)
                                 theta1)
                     (func,"Substitution list theorem LHS does not equal \
                            matching subterm")
        let () = assert1 (forall (fun (v,tm) -> term_eq tm v) theta2)
                     (func,"Substitution list entry missing for template variable") in
        internal_err func

(* subst_rule : (term * thm) list -> term -> thm -> thm                       *)
(*                                                                            *)
(* This is the template substitution rule.  It takes a substitution scheme    *)
(* (in the form of an association list and a template term) followed by a     *)
(* theorem, and performs a single parallel substitution of free subterms in   *)
(* the theorem's conclusion, according to the substitution scheme.  The       *)
(* template term determines which free occurrences of equality theorem LHSs   *)
(* in the supplied theorem get replaced, and reflects the syntactic structure *)
(* of the theorem's conclusion, except having template variable atoms in      *)
(* place of subterms due for replacement.  The association list maps each     *)
(* template variable to an equality theorem, with equality theorem LHS for    *)
(* the supplied theorem's original subterm and RHS for the subterm that       *)
(* replaces it.  The resulting theorem has the unioned assumptions of all the *)
(* supplied theorems (regardless of whether they apply to the supplied        *)
(* template).                                                                 *)
(*                                                                            *)
(* Abstraction variables in the resulting theorem are renamed as necessary to *)
(* avoid variable capture.  Note that if two entries appear in the            *)
(* association list for the same template variable, then the earlier entry    *)
(* gets used, and that entries for variables that don't appear in the         *)
(* template are ignored.  If no entries apply, then the returned theorem's    *)
(* conclusion is the same as the input's.                                     *)
(*                                                                            *)
(*      `v1`            `v2`          ..                                      *)
(*    A1 |- s1 = t1   A2 |- s2 = t2   ..   `t`   A |- t[s1/v1,s2/v2,..]       *)
(*    -----------------------------------------------------------------       *)
(*                   A1 u A2 u .. |- t[t1/v1,t2/v2,..]                        *)

let subst_rule vths tmp th =
    let th1 = try2 (subst_conv vths tmp) (concl th)       "subst_rule"
    eq_mp_rule th1 th

(* ** META CONVERSIONS/RULES ** *)


(* Conversion rule *)

let conv_rule conv th = eq_mp_rule (conv (concl th)) th

/// Force module evaluation
let load = 
    get_all_axioms ()
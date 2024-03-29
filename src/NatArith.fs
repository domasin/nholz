﻿(* ========================================================================== *)
(* NATURAL NUMBER ARITHMETIC (HOL Zero)                                       *)
(* - Theory defining natural number operators/numerals; derived properties    *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2009-2012                            *)
(* ========================================================================== *)

(* ========================================================================== *)
(* F# Porting                                                                 *)
(*                                                                            *)
(* by Domenico Masini 2013                                                    *)
(* http://github.com/domasin/nholz                                        *)
(* ========================================================================== *)

///This module defines some classic natural number arithmetic operators,  
///using recursive function definition and the "SUC" and "ZERO" constants,
///and proves various basic properties about each operator.               
[<AutoOpen>]
module HOL.NatArith

(* HOL variables *)

let l = (parse_term(@"l:nat"))
let m = (parse_term(@"m:nat"))
let n = (parse_term(@"n:nat"))


(* ** ADDITION ** *)


(* Definition *)

set_fixity ("+", Infix (50,LeftAssoc))

/// |- (!n. 0 + n = n) /\ (!m n. SUC m + n = SUC (m + n))
let add_def =
    new_recursive_fun_definition nat_recursion_thm
     (parse_term(@"(!n. 0 + n = n) /\
          (!m n. (SUC m) + n = SUC (m + n))"))

let add_fn = (parse_term(@"$+"))

(* Syntax functions *)

let dest_add = dest_cbin "+"

let mk_add (tm1,tm2) = mk_bin (add_fn,tm1,tm2)

let is_add = can dest_add


(* add_left_id_lemma                                                          *)
(*                                                                            *)
(*    |- !n. 0 + n = n                                                        *)

let add_left_id_lemma = conjunct1_rule add_def


(* add_dist_left_suc_thm                                                      *)
(*                                                                            *)
(*    |- !m n. (SUC m) + n = SUC (m + n)                                      *)

let add_dist_left_suc_thm = 
    save_thm ("add_dist_left_suc_thm",
      conjunct2_rule add_def
    )

(* add_dist_right_suc_thm                                                     *)
(*                                                                            *)
(*    |- !m n. m + (SUC n) = SUC (m + n)                                      *)

let add_dist_right_suc_thm = 
    save_thm ("add_dist_right_suc_thm",
      (* |- !m n. m + (SUC n) = SUC (m + n)          *)
      list_gen_rule [m;n] (spec_rule m
        (mp_rule
          (bspec_rule (parse_term(@"\m. m + SUC n = SUC (m + n)")) nat_induction_thm)
          (conj_rule
            (* |- !n. 0 + SUC n = SUC (0 + n)                  *)
            (trans_rule
              (spec_rule (parse_term(@"SUC n")) add_left_id_lemma)
              (sym_rule
                (mk_comb2_rule (parse_term(@"SUC")) (spec_rule n add_left_id_lemma))))
            (* |- !m n. m + SUC n = SUC(m + n) ==> SUC m + SUC n = SUC(SUC m + n) *)
            (gen_rule m
              (disch_rule (parse_term(@"m + SUC n = SUC (m + n)"))
                (trans_rule
                  (* |- SUC m + SUC n = SUC (m + SUC n) *)
                  (list_spec_rule [m;(parse_term(@"SUC n"))] add_dist_left_suc_thm)
                  (* m + SUC n = SUC(m + n) |- SUC(m + SUC n) = SUC(SUC m + n)  *)
                  (mk_comb2_rule (parse_term(@"SUC"))
                    (trans_rule
                      (assume_rule (parse_term(@"m + SUC n = SUC (m + n)")))
                      (sym_rule
                        (list_spec_rule [m;n] add_dist_left_suc_thm) )))))))))
    )

(* add_id_thm                                                                 *)
(*                                                                            *)
(*    |- !n. n + 0 = n                                                        *)

let add_id_thm = 
    save_thm ("add_id_thm",
      (* !n. n + 0 = n                        *)
      mp_rule
        (bspec_rule (parse_term(@"\n. n + 0 = n")) nat_induction_thm)
        (conj_rule
          (* |- 0 + 0 = 0                          *)
          (spec_rule (parse_term(@"0")) add_left_id_lemma)
          (* |- !n. n + 0 = n ==> SUC n + 0 = SUC n    *)
          (gen_rule n
            (disch_rule (parse_term(@"n + 0 = n"))
              (trans_rule
                (* |- SUC n + 0 = SUC (n + 0)                *)
                (list_spec_rule [n;(parse_term(@"0"))] add_dist_left_suc_thm)
                (* n + 0 = n |- SUC (n + 0) = SUC n          *)
                (mk_comb2_rule (parse_term(@"SUC")) (assume_rule (parse_term(@"n + 0 = n"))) )))))
    )

(* add_comm_thm                                                               *)
(*                                                                            *)
(*    |- !m n. m + n = n + m                                                  *)

let add_comm_thm = 
    save_thm ("add_comm_thm",
      (* |- !m n. m + n = n + m                  *)
      gen_rule m
        (mp_rule
          (bspec_rule (parse_term(@"\n. m + n = n + m")) nat_induction_thm)
          (conj_rule
            (* |- m + 0 = 0 + m                                  *)
            (trans_rule
              (spec_rule m add_id_thm)
              (sym_rule (spec_rule m add_left_id_lemma)) )
            (* |- !n. m + n = n + m ==> m + SUC n = SUC n + m    *)
            (gen_rule n
              (disch_rule (parse_term(@"m + n = n + m"))
                (list_trans_rule
                  [(* |- m + SUC n = SUC (m + n)                     *)
                   list_spec_rule [m;n] add_dist_right_suc_thm;
                   (* m + n = n + m |- ... = SUC (n + m)             *)
                   mk_comb2_rule (parse_term(@"SUC")) (assume_rule (parse_term(@"m + n = n + m")));
                   (* |- ...               = SUC n + m               *)
                   sym_rule (list_spec_rule [n;m] add_dist_left_suc_thm)
                  ])))))
    )

//  add_assoc_thm                          
//                                         
/// |- !l m n. l + (m + n) = (l + m) + n
let add_assoc_thm = 
    save_thm ("add_assoc_thm",
      list_gen_rule [(parse_term(@"l:nat"));m]
        (mp_rule
          (bspec_rule (parse_term(@"\n. l + (m + n) = (l + m) + n")) nat_induction_thm)
          (conj_rule
            (* |- l + (m + 0) = (l + m) + 0     *)
            (trans_rule
              (mk_comb2_rule (parse_term(@"$+ l")) (spec_rule m add_id_thm))
              (sym_rule (spec_rule (parse_term(@"l+m")) add_id_thm)))
            (* |- !n. l + (m + n) = (l + m) + n                       *)
            (*           ==> l + (m + SUC n) = (l + m) + SUC n        *)
            (gen_rule n
              (disch_rule (parse_term(@"l + (m + n) = (l + m) + n"))
                (list_trans_rule
                  [(* |- l + (m + SUC n) = l + SUC (m + n)                *)
                   mk_comb2_rule (parse_term(@"$+ l"))
                         (list_spec_rule [m;n] add_dist_right_suc_thm);
                   (* |- ...             = SUC (l + (m + n))              *)
                   list_spec_rule [(parse_term(@"l:nat"));(parse_term(@"m+n"))] add_dist_right_suc_thm;
                   (* l + (m + n) = l + m + n                             *)
                   (*    |- ...          = SUC ((l + m) + n)              *)
                   mk_comb2_rule (parse_term(@"SUC")) (assume_rule (parse_term(@"l + (m + n) = (l + m) + n")));
                   (* |- ...             = (l + m) + SUC n                *)
                   sym_rule (list_spec_rule [(parse_term(@"l+m"));n] add_dist_right_suc_thm)
                  ])))))
    )

(* suc_add_thm                                                                *)
(*                                                                            *)
(*    |- !n. SUC n = n + 1                                                    *)

let suc_add_thm = 
    save_thm ("suc_add_thm",
      (* |- !n. SUC n = n + SUC 0                 *)
      gen_rule n
        (list_trans_rule
          [ (* |- SUC n = SUC (n + 0)               *)
            sym_rule (mk_comb2_rule (parse_term(@"SUC")) (spec_rule n add_id_thm));
            (* |- ...   = n + SUC 0                 *)
            sym_rule (list_spec_rule [n;(parse_term(@"0"))] add_dist_right_suc_thm);
            (* |- ...   = n + 1                     *)
            mk_bin2_rule (parse_term(@"$+")) n suc_zero_thm ])
    )

(* add_switch_lemma                                                           *)
(*                                                                            *)
(*   |- !w x y z. (w + x) + (y + z) = (w + y) + (x + z)                       *)

let (w,x,y,z) = ((parse_term(@"w:nat")),(parse_term(@"x:nat")),(parse_term(@"y:nat")),(parse_term(@"z:nat")))

let add_switch_lemma = 
    save_lemma ("add_switch_lemma",
      list_gen_rule [w;x;y;z]
        (list_trans_rule
           [ (* |- (w + x) + (y + z) = w + (x + (y + z))     *)
             sym_rule (list_spec_rule [w;x;(parse_term(@"y+z"))] add_assoc_thm);
             (* |- ...               = w + ((x + y) + z)     *)
             mk_bin2_rule (parse_term(@"$+")) w (list_spec_rule [x;y;z] add_assoc_thm);
             (* |- ...               = w + ((y + x) + z)     *)
             mk_bin2_rule (parse_term(@"$+")) w
               (mk_bin1_rule (parse_term(@"$+")) (list_spec_rule [x;y] add_comm_thm) z);
             (* |- ...               = w + (y + (x + z))     *)
             sym_rule
               (mk_bin2_rule (parse_term(@"$+")) w (list_spec_rule [y;x;z] add_assoc_thm));
             (* |- ...               = (w + y) + (x + z)     *)
             list_spec_rule [w;(parse_term(@"y:nat"));(parse_term(@"x+z"))] add_assoc_thm ])
    )


(* ** PREDECESSOR ** *)


(* Definition *)

/// |- PRE 0 = 0 /\ (!n. PRE (SUC n) = n)
let pre_def =
    new_recursive_fun_definition nat_recursion_thm
        (parse_term(@"(PRE 0 = 0) /\ (!n. PRE (SUC n) = n)"))

let pre_fn = (parse_term(@"PRE"))

(* Syntax functions *)

let dest_pre tm =
    try
        let (tm1,tm2) = dest_comb tm in
        let () = assert0 (tm1 = pre_fn)     LocalFail in
        tm2
    with HolFail _ | LocalFail -> hol_fail ("dest_pre", "Not a PRE expression")

let mk_pre tm = mk_comb (pre_fn,tm)

let is_pre = can dest_pre


(* pre_suc_thm                                                                *)
(*                                                                            *)
(*    |- !n. PRE (SUC n) = n                                                  *)

let pre_suc_thm = 
    save_thm ("pre_suc_thm",
      conjunct2_rule pre_def
    )

(* pre_zero_thm                                                               *)
(*                                                                            *)
(*    |- PRE 0 = 0                                                            *)

let pre_zero_thm = 
    save_thm ("pre_zero_thm",
      conjunct1_rule pre_def
    )


(* ** SUBTRACTION ** *)


(* Definition *)

set_fixity ("-", Infix (50,LeftAssoc))


/// |- (!n. n - 0 = n) /\ (!m n. m - SUC n = PRE (m - n))
let sub_def =
    new_recursive_fun_definition nat_recursion_thm
        (parse_term(@"(!n. n - 0 = n) /\ (!m n. m - (SUC n) = PRE (m - n))"))

let sub_fn = (parse_term(@"$-"))


(* Syntax functions *)

let dest_sub = dest_cbin "-"

let mk_sub (tm1,tm2) = mk_bin (sub_fn,tm1,tm2)

let is_sub = can dest_sub


(* sub_right_id_thm                                                           *)
(*                                                                            *)
(*    |- !n. n - 0 = n                                                        *)

let sub_right_id_thm = 
    save_thm ("sub_right_id_thm",
      conjunct1_rule sub_def
    )

(* sub_dist_right_suc_thm                                                     *)
(*                                                                            *)
(*    |- !m n. m - SUC n = PRE (m - n)                                        *)

let sub_dist_right_suc_thm = 
    save_thm ("sub_dist_right_suc_thm",
      conjunct2_rule sub_def
    )

(* suc_sub_suc_thm                                                            *)
(*                                                                            *)
(*    |- !m n. SUC m - SUC n = m - n                                          *)

let suc_sub_suc_thm = 
    save_thm ("suc_sub_suc_thm",
      gen_rule m
        (mp_rule
          (bspec_rule (parse_term(@"\n. SUC m - SUC n = m - n")) nat_induction_thm)
          (conj_rule
            (* |- SUC m - SUC 0 = m - 0                   *)
            (list_trans_rule
               [ (* |- SUC m - SUC 0 = PRE (SUC m - 0)      *)
                 list_spec_rule [(parse_term(@"SUC m"));(parse_term(@"0"))] sub_dist_right_suc_thm;
                 (* |- ...           = PRE (SUC m)          *)
                 mk_comb2_rule (parse_term(@"PRE")) (spec_rule (parse_term(@"SUC m")) sub_right_id_thm);
                 (* |- ...           = m                    *)
                 spec_rule m pre_suc_thm;
                 (* |- ...           = m - 0                *)
                 sym_rule (spec_rule m sub_right_id_thm) ])
            (* |- !n. SUC m - SUC n = m - n ==> SUC m - SUC (SUC n) = m - SUC n  *)
            (gen_rule n
              (disch_rule (parse_term(@"SUC m - SUC n = m - n"))
                (* SUC m - SUC n = m - n |- (SUC m) - SUC (SUC n) = m - SUC n  *)
                (list_trans_rule
                   [ (* |- (SUC m) - SUC (SUC n) = PRE ((SUC m) - (SUC n))   *)
                     list_spec_rule [(parse_term(@"SUC m"));(parse_term(@"SUC n"))] sub_dist_right_suc_thm;
                     (* SUC m - SUC n = m - n |- ... = PRE (m - n)           *)
                     mk_comb2_rule (parse_term(@"PRE")) (assume_rule (parse_term(@"(SUC m) - (SUC n) = m - n")));
                     (* |- ...                       = m - SUC n             *)
                     sym_rule (list_spec_rule [m;n] sub_dist_right_suc_thm)
                   ] )))))
    )

(* sub_cancel_thm                                                             *)
(*                                                                            *)
(*    |- !n. n - n = 0                                                        *)

let sub_cancel_thm = 
    save_thm ("sub_cancel_thm",
      mp_rule
        (bspec_rule (parse_term(@"\n. n - n = 0")) nat_induction_thm)
        (conj_rule
          (* |- 0 - 0 = 0                               *)
          (spec_rule (parse_term(@"0")) sub_right_id_thm)
          (* |- !n. n - n = 0 ==> SUC n - SUC n = 0     *)
          (gen_rule n
            (disch_rule (parse_term(@"n - n = 0"))
              (trans_rule
                (* |- SUC n - SUC n = n - n                 *)
                (list_spec_rule [n;n] suc_sub_suc_thm)
                (* |- ...           = 0                     *)
                (assume_rule (parse_term(@"n - n = 0"))) ))))
    )

(* add_sub_cancel_thm                                                         *)
(*                                                                            *)
(*    |- !m n. (m + n) - n = m                                                *)

let add_sub_cancel_thm = 
    save_thm ("add_sub_cancel_thm",
      gen_rule m
        (mp_rule
          (bspec_rule (parse_term(@"\n. (m + n) - n = m")) nat_induction_thm)
          (conj_rule
            (* |- (m + 0) - 0 = m                                   *)
            (trans_rule
              (mk_bin1_rule (parse_term(@"$-")) (spec_rule m add_id_thm) (parse_term(@"0")))
              (spec_rule m sub_right_id_thm) )
            (* |- !n. (m + n) - n = m ==> (m + SUC n) - SUC n = m   *)
            (gen_rule n
              (disch_rule (parse_term(@"(m + n) -n = m"))
                (* (m + n) - n = m |- (m + SUC n) - SUC n = m         *)
                (list_trans_rule
                   [ (* |- (m + SUC n) - SUC n = SUC (m + n) - SUC n    *)
                     mk_bin1_rule (parse_term(@"$-"))
                       (list_spec_rule [m;n] add_dist_right_suc_thm) (parse_term(@"SUC n"));
                     (* |- ...                 = (m + n) - n            *)
                     list_spec_rule [(parse_term(@"m+n"));n] suc_sub_suc_thm;
                     (* (m + n) - n = m |- ... = m                      *)
                     assume_rule (parse_term(@"(m + n) -n = m")) ] )))))
    )


(* ** MULTIPLICATION ** *)


(* Definition *)

set_fixity ("*", Infix (55,LeftAssoc))

/// |- (!n. 0 * n = 0) /\ (!m n. SUC m * n = n + m * n)
let mult_def =
    new_recursive_fun_definition nat_recursion_thm
        (parse_term(@"(!n. 0 * n = 0) /\ (!m n. (SUC m) * n = n + (m * n))"))

let mult_fn = (parse_term(@"$*"))


(* Syntax functions *)

let dest_mult = dest_cbin "*"

let mk_mult (tm1,tm2) = mk_bin (mult_fn,tm1,tm2)

let is_mult = can dest_mult


(* mult_left_zero_lemma                                                       *)
(*                                                                            *)
(*    |- !n. 0 * n = 0                                                        *)

let mult_left_zero_lemma = conjunct1_rule mult_def


(* mult_dist_left_suc_thm                                                     *)
(*                                                                            *)
(*    |- !m n. (SUC m) * n = n + (m * n)                                      *)

let mult_dist_left_suc_thm = 
    save_thm ("mult_dist_left_suc_thm",
      conjunct2_rule mult_def
    )

(* mult_zero_thm                                                              *)
(*                                                                            *)
(*    |- !n. n * 0 = 0                                                        *)

let mult_zero_thm = 
    save_thm ("mult_zero_thm",
      mp_rule
        (bspec_rule (parse_term(@"\n. n * 0 = 0")) nat_induction_thm)
        (conj_rule
          (* |- 0 * 0 = 0                           *)
          (spec_rule (parse_term(@"0")) mult_left_zero_lemma)
          (* |- !n. n * 0 = 0 ==> SUC n * 0 = 0     *)
          (gen_rule n
            (disch_rule (parse_term(@"n * 0 = 0"))
              (list_trans_rule
                [ (* |- SUC n * 0 = 0 + n * 0           *)
                  list_spec_rule [n;(parse_term(@"0"))] mult_dist_left_suc_thm;
                  (* |- ...       = n * 0               *)
                  spec_rule (parse_term(@"n * 0")) add_left_id_lemma;
                  (* n * 0 = 0 |- ... = 0               *)
                  assume_rule (parse_term(@"n * 0 = 0")) ]))))
    )

(* mult_dist_right_suc_thm                                                    *)
(*                                                                            *)
(*    |- !m n. m * SUC n = m + (m * n)                                        *)

let mult_dist_right_suc_thm = 
    save_thm ("mult_dist_right_suc_thm",
      list_gen_rule [m;n] (spec_rule m
        (mp_rule
          (bspec_rule (parse_term(@"\m. m * SUC n = m + (m * n)")) nat_induction_thm)
          (conj_rule
            (* |- 0 * SUC n = 0 + (0 * n)                      *)
            (list_trans_rule
               [ spec_rule (parse_term(@"SUC n")) mult_left_zero_lemma;
                 sym_rule (spec_rule n mult_left_zero_lemma);
                 sym_rule (spec_rule (parse_term(@"0 * n")) add_left_id_lemma) ] )
            (* |- !m. m * SUC n = m + m * n ==> SUC m * SUC n = SUC m + SUC m * n *)
            (gen_rule m
              (disch_rule (parse_term(@"m * SUC n = m + m * n"))
                (list_trans_rule
                  [ (* |- SUC m * SUC n = SUC n + m * SUC n             *)
                     list_spec_rule [m;(parse_term(@"SUC n"))] mult_dist_left_suc_thm;
                     (* m * SUC n = m + m * n                           *)
                     (*      |- ...     = SUC n + (m + m * n)           *)
                     mk_bin2_rule (parse_term(@"$+")) (parse_term(@"SUC n"))
                        (assume_rule (parse_term(@"m * SUC n = m + m * n")));
                     (* |- ...          = (SUC n + m) + m * n           *)
                     list_spec_rule [(parse_term(@"SUC n"));m;(parse_term(@"m*n"))] add_assoc_thm;
                     (* |- ...          = (SUC m + n) + m * n           *)
                     mk_bin1_rule (parse_term(@"$+"))
                       (* |- SUC n + m = SUC m + n                        *)
                       (list_trans_rule
                          [ list_spec_rule [n;m] add_dist_left_suc_thm;
                            sym_rule (list_spec_rule [n;m] add_dist_right_suc_thm);
                            list_spec_rule [n;(parse_term(@"SUC m"))] add_comm_thm ])
                       (parse_term(@"m*n"));
                     (* |- ...          = SUC m + (n + m * n)           *)
                     sym_rule (list_spec_rule [(parse_term(@"SUC m"));n;(parse_term(@"m*n"))] add_assoc_thm);
                     (* |- ...          = SUC m + SUC m * n             *)
                     mk_bin2_rule (parse_term(@"$+")) (parse_term(@"SUC m"))
                       (sym_rule (list_spec_rule [m;n] mult_dist_left_suc_thm))
                   ]))))))
    )

(* mult_comm_thm                                                              *)
(*                                                                            *)
(*    |- !m n. m * n = n * m                                                  *)

let mult_comm_thm = 
    save_thm ("mult_comm_thm",
      (* |- !m n. m * n = n * m                          *)
      gen_rule m
        (mp_rule
          (bspec_rule (parse_term(@"\n. m * n = n * m")) nat_induction_thm)
          (conj_rule
            (* |- m * 0 = 0 * m                                 *)
            (trans_rule (spec_rule m mult_zero_thm)
                        (sym_rule (spec_rule m mult_left_zero_lemma)))
            (* |- !n. m * n = n * m ==> m * SUC n = SUC n * m   *)
            (gen_rule n
              (disch_rule (parse_term(@"m * n = n * m"))
                (list_trans_rule
                   [ (* |- m * SUC n = m + (m * n)                  *)
                     list_spec_rule [m;n] mult_dist_right_suc_thm;
                     (* m * n = n * m |- ... = m + n * m            *)
                     (mk_bin2_rule (parse_term(@"$+")) m (assume_rule (parse_term(@"m * n = n * m"))));
                     (* |- ...               = SUC n * m            *)
                     (sym_rule
                       (list_spec_rule [n;m] mult_dist_left_suc_thm)) ])))))
    )

(* mult_dist_left_add_thm                                                     *)
(*                                                                            *)
(*    |- !l m n. (l + m) * n = l * n + m * n                                  *)

let mult_dist_left_add_thm = 
    save_thm ("mult_dist_left_add_thm",
      list_gen_rule [l;m]
        (mp_rule
          (bspec_rule (parse_term(@"\n. (l + m) * n = l * n + m * n")) nat_induction_thm)
          (conj_rule
            (* |- (l + m) * 0 = l * 0 + m * 0                    *)
            (list_trans_rule
               [ spec_rule (parse_term(@"l+m")) mult_zero_thm;
                 sym_rule (spec_rule (parse_term(@"0")) add_id_thm);
                 sym_rule
                   (mk_bin_rule (parse_term(@"$+"))
                     (spec_rule l mult_zero_thm)
                     (spec_rule m mult_zero_thm)) ])
            (* |- !n. (l + m) * n = l * n + m * n ==>                     *)
            (*                   (l + m) * SUC n = l * SUC n + m * SUC n  *)
            (gen_rule n
              (disch_rule (parse_term(@"(l + m) * n = l * n + m * n"))
                (list_trans_rule
                   [ (* |- (l + m) * SUC n = (l + m) + (l + m) * n          *)
                     list_spec_rule [(parse_term(@"l+m"));n] mult_dist_right_suc_thm;
                     (* (l + m) * n = l * n + m * n                         *)
                     (*    |- ...          = (l + m) + (l * n + m * n)      *)
                     mk_bin2_rule (parse_term(@"$+")) (parse_term(@"(l+m)"))
                       (assume_rule (parse_term(@"(l + m) * n = l * n + m * n")));
                     (* |- ...             = (l + l * n) + (m + m * n)      *)
                     list_spec_rule [l;m;(parse_term(@"l*n"));(parse_term(@"m*n"))] add_switch_lemma;
                     (* |- ...             = l * SUC n + m * SUC n          *)
                     sym_rule
                       (mk_bin_rule (parse_term(@"$+"))
                         (list_spec_rule [l;n] mult_dist_right_suc_thm)
                         (list_spec_rule [m;n] mult_dist_right_suc_thm)) ])))))
    )

(* mult_dist_right_add_thm                                                    *)
(*                                                                            *)
(*    |- !l m n. l * (m + n) = l * m + l * n                                  *)

let mult_dist_right_add_thm = 
    save_thm ("mult_dist_right_add_thm",
      list_gen_rule [l;m;n]
        (list_trans_rule
           [ (* |- l * (m + n) = (m + n) * l           *)
             list_spec_rule [l;(parse_term(@"m+n"))] mult_comm_thm;
             (* |- ...         = m * l + n * l         *)
             list_spec_rule [m;n;l] mult_dist_left_add_thm;
             (* |- ...         = l * m + l * n         *)
             mk_bin_rule (parse_term(@"$+"))
               (list_spec_rule [m;l] mult_comm_thm)
               (list_spec_rule [n;l] mult_comm_thm) ] )
    )

(* mult_assoc_thm                                                             *)
(*                                                                            *)
(*    |- !l m n. l * (m * n) = (l * m) * n                                    *)

let mult_assoc_thm = 
    save_thm ("mult_assoc_thm",
      list_gen_rule [l;m]
        (mp_rule
          (bspec_rule (parse_term(@"\n. l * (m * n) = (l * m) * n")) nat_induction_thm)
          (conj_rule
            (* |- l * (m * 0) = (l * m) * 0      *)
            (list_trans_rule
               [ (* |- l * (m * 0) = l * 0                *)
                 mk_comb2_rule (parse_term(@"$* l")) (spec_rule m mult_zero_thm);
                 (* |- ...         = 0                    *)
                 spec_rule l mult_zero_thm;
                 (* |- ...         = (l * m) * 0          *)
                 sym_rule (spec_rule (parse_term(@"l*m")) mult_zero_thm) ])
            (* |- !n. l * (m * n) = (l * m) * n ==>                       *)
            (*                l * (m * SUC n) = (l * m) * SUC n           *)
            (gen_rule n
              (disch_rule (parse_term(@"l * (m * n) = (l * m) * n"))
                (list_trans_rule
                   [ (* |- l * (m * SUC n) = l * (m + m * n)        *)
                     mk_bin2_rule (parse_term(@"$*")) l
                       (list_spec_rule [m;n] mult_dist_right_suc_thm);
                     (* |- ...             = l * m + l * (m * n)    *)
                     list_spec_rule [l;m;(parse_term(@"m*n"))] mult_dist_right_add_thm;
                     (* |- ...             = l * m + (l * m) * n    *)
                     mk_bin2_rule (parse_term(@"$+")) (parse_term(@"l*m"))
                       (assume_rule (parse_term(@"l * (m * n) = (l * m) * n")));
                     (* |- ...             = (l * m) * SUC n        *)
                     sym_rule
                       (list_spec_rule [(parse_term(@"l*m"));n] mult_dist_right_suc_thm) ])))))
    )

(* mult_left_flip_lemma                                                       *)
(*                                                                            *)
(*    |- !x y z. x * (y * z) = y * (x * z)                                    *)

let mult_left_flip_lemma = 
    save_lemma ("mult_left_flip_lemma",
      list_gen_rule [x;y;z]
        (list_trans_rule
           [ (* |- x * (y * z) = (x * y) * z       *)
             list_spec_rule [x;y;z] mult_assoc_thm;
             (* |- (x * y) * z = (y * x) * z       *)
             mk_bin1_rule (parse_term(@"$*")) (list_spec_rule [x;y] mult_comm_thm) z;
             (* |- (y * x) * z = y * (x * z)       *)
             sym_rule (list_spec_rule [y;x;z] mult_assoc_thm) ])
    )

(* mult_id_thm                                                                *)
(*                                                                            *)
(*    |- !n. n * 1 = n                                                        *)

let mult_id_thm = 
    save_thm ("mult_id_thm",
      gen_rule n
        (list_trans_rule
           [ (* |- n * 1 = n * SUC 0            *)
             mk_bin2_rule (parse_term(@"$*")) n (sym_rule suc_zero_thm);
             (* |- ...   = n + n * 0            *)
             list_spec_rule [n;zero_tm] mult_dist_right_suc_thm;
             (* |- ...   = n + 0                *)
             mk_bin2_rule (parse_term(@"$+")) n (spec_rule n mult_zero_thm);
             (* |- ...   = n                    *)
             spec_rule n add_id_thm ])
    )

(* mult_left_id_lemma                                                         *)
(*                                                                            *)
(*    |- !n. 1 * n = n                                                        *)

let mult_left_id_lemma =
  gen_rule n
    (trans_rule
      (* |- 1 * n = n * 1                                *)
      (list_spec_rule [(parse_term(@"1"));n] mult_comm_thm)
      (* |- n * 1 = n                                    *)
      (spec_rule n mult_id_thm))

(* twice_thm                                                                  *)
(*                                                                            *)
(*    |- !n. 2 * n = n + n                                                    *)

let twice_thm = 
    save_thm ("twice_thm",
      gen_rule n
        (list_trans_rule
           [ (* |- 2 * n = (SUC 1) * n       *)
             sym_rule (mk_bin1_rule (parse_term(@"$*")) suc_one_thm n);
             (* |- ...   = n + 1 * n         *)
             list_spec_rule [(parse_term(@"1"));n] mult_dist_left_suc_thm;
             (* |- ...   = n + n             *)
             mk_bin2_rule (parse_term(@"$+")) n (spec_rule n mult_left_id_lemma) ])
    )


(* ** EXPONENTIATION ** *)


(* Definition *)

set_fixity ("EXP", Infix (60,LeftAssoc))

/// |- (!n. n EXP 0 = 1) /\ (!m n. m EXP SUC n = m * m EXP n)
let exp_def =
  new_recursive_fun_definition nat_recursion_thm
   (parse_term(@"(!n. n EXP 0 = 1) /\ (!m n. m EXP (SUC n) = m * m EXP n)"))

let exp_fn = (parse_term(@"$EXP"))

(* Syntax functions *)

let dest_exp = dest_cbin "EXP"

let mk_exp (tm1,tm2) = mk_bin (exp_fn,tm1,tm2)

let is_exp = can dest_exp

(* exp_right_zero_thm                                                         *)
(*                                                                            *)
(*    |- !n. n EXP 0 = 1                                                      *)

let exp_right_zero_thm = 
    save_thm ("exp_right_zero_thm",
      conjunct1_rule exp_def
    )

(* exp_dist_right_suc_thm                                                     *)
(*                                                                            *)
(*    |- !m n. m EXP (SUC n) = m * m EXP n                                    *)

let exp_dist_right_suc_thm = 
    save_thm ("exp_dist_right_suc_thm",
      conjunct2_rule exp_def
    )

(* exp_right_id_thm                                                           *)
(*                                                                            *)
(*    |- !n. n EXP 1 = n                                                      *)

let exp_right_id_thm = 
    save_thm ("exp_right_id_thm",
      gen_rule n
        (list_trans_rule
           [ (* |- n EXP 1 = n EXP (SUC 0)         *)
             mk_bin2_rule (parse_term(@"$EXP")) n (sym_rule suc_zero_thm);
             (* |- ...     = n * n EXP 0           *)
             list_spec_rule [n;(parse_term(@"0"))] exp_dist_right_suc_thm;
             (* |- ...     = n * 1                 *)
             mk_bin2_rule (parse_term(@"$*")) n (spec_rule n exp_right_zero_thm);
             (* |- ...     = n                     *)
             spec_rule n mult_id_thm ])
    )

(* exp_dist_right_add_thm                                                     *)
(*                                                                            *)
(*    |- !l m n. l EXP (m + n) = (l EXP m) * (l EXP n)                        *)

let exp_dist_right_add_thm = 
    save_thm ("exp_dist_right_add_thm",
      list_gen_rule [l;m]
        (mp_rule
          (bspec_rule (parse_term(@"\n. l EXP (m + n) = (l EXP m) * (l EXP n)")) nat_induction_thm)
          (conj_rule
            (* |- l EXP (m + 0) = l EXP m * l EXP 0          *)
            (list_trans_rule
               [ (* |- l EXP (m + 0) = l EXP m                 *)
                 mk_bin2_rule (parse_term(@"$EXP")) l (spec_rule m add_id_thm);
                 (* |- ...           = (l EXP m) * 1           *)
                 sym_rule (spec_rule (parse_term(@"l EXP m")) mult_id_thm);
                 (* |- ...           = (l EXP m) * (l EXP 0)   *)
                 sym_rule
                   (mk_bin2_rule (parse_term(@"$*")) (parse_term(@"l EXP m")) (spec_rule l exp_right_zero_thm))])
            (* |- !n. l EXP (m + n) = l EXP m * l EXP n ==>          *)
            (*           l EXP (m + SUC n) = l EXP m * l EXP (SUC n) *)
            (gen_rule n
              (disch_rule (parse_term(@"l EXP (m + n) = l EXP m * l EXP n"))
                (list_trans_rule
                   [ (* |- l EXP (m + SUC n) = l EXP (SUC (m + n))          *)
                     mk_bin2_rule (parse_term(@"$EXP")) l
                       (list_spec_rule [m;n] add_dist_right_suc_thm);
                     (* |- ...               = l * l EXP (m + n)            *)
                     list_spec_rule [l;(parse_term(@"m+n"))] exp_dist_right_suc_thm;
                     (* |- ...               = l * (l EXP m * l EXP n)      *)
                     mk_bin2_rule (parse_term(@"$*")) l
                       (assume_rule (parse_term(@"l EXP (m + n) = l EXP m * l EXP n")));
                     (* |- ...               = l EXP m * (l * l EXP n)      *)
                     list_spec_rule [l;(parse_term(@"l EXP m"));(parse_term(@"l EXP n"))] mult_left_flip_lemma;
                     (* |- ...               = l EXP m * (l EXP (SUC n))    *)
                     sym_rule
                       (mk_bin2_rule (parse_term(@"$*")) (parse_term(@"l EXP m"))
                         (list_spec_rule [l;n] exp_dist_right_suc_thm) ) ])))))
    )

(* ** EVEN AND ODD ** *)


(* Definitions *)

/// |- (EVEN 0 <=> true) /\ (!n. EVEN (SUC n) <=> ~ EVEN n)
let even_def =
  new_recursive_fun_definition nat_recursion_thm
    (parse_term(@"(EVEN 0 <=> true) /\ (!n. EVEN (SUC n) <=> ~ (EVEN n))"))

let even_fn = (parse_term(@"EVEN"))

/// |- !n. ODD n <=> ~ EVEN n
let odd_def =
    new_fun_definition  (parse_term(@"!n. ODD n <=> ~ (EVEN n)"))

let odd_fn = (parse_term(@"ODD"))

let dest_even tm =
    try
        let (tm1,tm2) = dest_comb tm in
        let () = assert0 (tm1 = even_fn)     LocalFail in
        tm2
    with HolFail _ | LocalFail -> hol_fail ("dest_even","Not an EVEN expression")

let mk_even tm = mk_comb (even_fn,tm)

let is_even = can dest_even

let dest_odd tm =
    try
        let (tm1,tm2) = dest_comb tm in
        let () = assert0 (tm1 = odd_fn)     LocalFail in
        tm2
    with HolFail _ | LocalFail -> hol_fail ("dest_odd","Not an ODD expression")

let mk_odd tm = mk_comb (odd_fn,tm)

let is_odd = can dest_odd

(* zero_even_thm                                                              *)
(*                                                                            *)
(*    |- EVEN 0                                                               *)

let zero_even_thm = 
    save_thm ("zero_even_thm",
      eqt_elim_rule (conjunct1_rule even_def)
    )

(* even_suc_thm                                                               *)
(*                                                                            *)
(*    |- !n. EVEN (SUC n) <=> ~ (EVEN n)                                      *)

let even_suc_thm = 
    save_thm ("even_suc_thm",
      conjunct2_rule even_def
    )

(* odd_suc_thm                                                                *)
(*                                                                            *)
(*    |- !n. ODD (SUC n) <=> ~ (ODD n)                                        *)

let odd_suc_thm = 
    save_thm ("odd_suc_thm",
      gen_rule n
        (trans_rule
          (* |- ODD (SUC n) <=> ~ EVEN (SUC n)   *)
          (spec_rule (parse_term(@"SUC n")) odd_def)
          (* |- ~ EVEN (SUC n) <=> ~ ODD n       *)
          (mk_not_rule
            (trans_rule
              (* |- EVEN (SUC n) <=> ~ EVEN n      *)
              (spec_rule n even_suc_thm)
              (* |- ~ EVEN n <=> ODD n             *)
              (sym_rule (spec_rule n odd_def)) )))
    )

(* zero_not_odd_thm                                                           *)
(*                                                                            *)
(*    |- ~ ODD 0                                                              *)

let zero_not_odd_thm = 
    save_thm ("zero_not_odd_thm",
      eqf_elim_rule
        (list_trans_rule
           [ (* |- ODD 0 <=> ~ EVEN 0             *)
             spec_rule (parse_term(@"0")) odd_def;
             (* |- ~ EVEN 0 <=> ~ true            *)
             mk_not_rule (eqt_intro_rule zero_even_thm);
             (* |- ~ true <=> false               *)
             not_true_thm ])
    )

(* one_odd_thm                                                                *)
(*                                                                            *)
(*    |- ODD 1                                                                *)

let one_odd_thm = 
    save_thm ("one_odd_thm",
      eq_mp_rule
        (* |- EVEN 0 <=> ODD 1              *)
        (sym_rule
          (trans_rule
             (* |- ODD 1 <=> ODD (SUC 0)        *)
             (sym_rule (mk_comb2_rule (parse_term(@"ODD")) suc_zero_thm))
             (* |- ODD (SUC 0) <=> ~ ODD 0      *)
             (spec_rule (parse_term(@"0")) odd_suc_thm) ))
        zero_not_odd_thm
    )

(* twice_suc_lemma                                                            *)
(*                                                                            *)
(*    |- !n. 2 * SUC n = SUC (SUC (2 * n))                                    *)

let twice_suc_lemma =
  gen_rule n
    (list_trans_rule
      [ (* |- 2 * SUC n = 2 + 2 * n                      *)
        list_spec_rule [(parse_term(@"2"));n] mult_dist_right_suc_thm;
        (* |- ...       = (SUC 1) + 2 * n                *)
        mk_bin1_rule (parse_term(@"$+")) (sym_rule suc_one_thm) (parse_term(@"2*n"));
        (* |- ...       = SUC (1 + 2 * n)                *)
        list_spec_rule [(parse_term(@"1"));(parse_term(@"2*n"))] add_dist_left_suc_thm;
        (* |- ...       = SUC (SUC (2 * n))              *)
        mk_comb2_rule (parse_term(@"SUC"))
          (trans_rule
            (list_spec_rule [(parse_term(@"1"));(parse_term(@"2*n"))] add_comm_thm)
            (sym_rule (spec_rule (parse_term(@"2*n")) suc_add_thm)) ) ])

(* twice_even_thm                                                             *)
(*                                                                            *)
(*    |- !n. EVEN (2 * n)                                                     *)

let twice_even_thm = 
    save_thm ("twice_even_thm",
      mp_rule
        (bspec_rule (parse_term(@"\n. EVEN (2 * n)")) nat_induction_thm)
        (conj_rule
          (* |- EVEN (2 * 0)                             *)
          (eq_mp_rule
            (sym_rule (mk_comb2_rule (parse_term(@"EVEN")) (spec_rule (parse_term(@"2")) mult_zero_thm)))
            zero_even_thm )
          (* |- !n. EVEN (2 * n) ==> EVEN (2 * SUC n)    *)
          (gen_rule n
            (eq_imp_rule2
              (list_trans_rule
                 [ (* |- EVEN (2 * SUC n) <=> EVEN (SUC (SUC (2 * n)))  *)
                   mk_comb2_rule (parse_term(@"EVEN")) (spec_rule n twice_suc_lemma);
                   (* |- ...              <=> ~ EVEN (SUC (2 * n))      *)
                   spec_rule (parse_term(@"SUC (2*n)")) even_suc_thm;
                   (* |- ...              <=> ~ ~ EVEN (2 * n)          *)
                   mk_not_rule (spec_rule (parse_term(@"2*n")) even_suc_thm);
                   (* |- ...              <=> EVEN (2 * n)              *)
                   spec_rule (parse_term(@"EVEN (2*n)")) not_dneg_thm ]))))
    )

(* suc_twice_odd_thm                                                          *)
(*                                                                            *)
(*    |- !n. ODD (SUC (2 * n))                                                *)

let suc_twice_odd_thm = 
    save_thm ("suc_twice_odd_thm",
      mp_rule
        (bspec_rule (parse_term(@"\n. ODD (SUC (2 * n))")) nat_induction_thm)
        (conj_rule
          (* |- ODD (SUC (2 * 0))                          *)
          (eq_mp_rule
            (sym_rule
              (mk_comb2_rule (parse_term(@"ODD"))
                (trans_rule
                  (mk_comb2_rule (parse_term(@"SUC")) (spec_rule (parse_term(@"2")) mult_zero_thm))
                  suc_zero_thm )))
            one_odd_thm )
          (* |- !n. ODD (SUC (2 * n)) ==> ODD (SUC (2 * SUC n))    *)
          (gen_rule n
            (eq_imp_rule2
              (list_trans_rule
                 [ (* |- ODD (SUC (2 * SUC n)) <=> ODD (SUC (SUC (SUC (2 * n))))  *)
                   mk_comb2_rule (parse_term(@"ODD"))
                     (mk_comb2_rule (parse_term(@"SUC")) (spec_rule n twice_suc_lemma));
                   (* |- ...              <=> ~ ODD (SUC (SUC (2 * n)))           *)
                   spec_rule (parse_term(@"SUC (SUC (2*n))")) odd_suc_thm;
                   (* |- ...              <=> ~ ~ ODD (SUC (2 * n))               *)
                   mk_not_rule (spec_rule (parse_term(@"SUC (2*n)")) odd_suc_thm);
                   (* |- ...              <=> ODD (SUC (2 * n))                   *)
                   spec_rule (parse_term(@"ODD (SUC (2*n))")) not_dneg_thm ]))))
    )

/// Force module evaluation
let load = 
    get_all_axioms ()
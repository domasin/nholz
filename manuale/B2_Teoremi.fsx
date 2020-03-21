(**
TEOREMI
=============

Lambda Calcolo
------------

**fun\_eq\_thm**

se due funzioni sono uguali, allora restituiscono lo stesso valore per ogni argomento e viceversa
*)

(***hide***)
#I "../bin/netstandard2.0"
#r "nholz.dll"
open HOL
fsi.AddPrinter print_type
fsi.AddPrinter print_qtype
fsi.AddPrinter print_term
fsi.AddPrinter print_qterm
fsi.AddPrinter print_thm
CoreThry.load
Equal.load
Bool.load
(***unhide***)

fun_eq_thm
// |- !(f:'a->'b) g. f = g <=> (!x. f x = g x)

let x = parse_term(@"x:'a") 
let f = parse_term(@"f:'a->'b")
let g = parse_term(@"g:'a->'b")

let th1 = parse_term(@"\x. (f:'a->'b) x") |> eta_conv  // 1                |- (\x. (f:'a->'b) x) = f                  
let th2 = sym_rule th1                                 // 2                |- (f:'a->'b) = (\x. f x)                  
let th3 = parse_term(@"!x. (f:'a->'b) x = g x") 
            |> assume_rule                             // 3  !x. f x = g x |- !x. f x = (g:'a->'b) x                  
let th4 = spec_rule x th3                              // 4  !x. f x = g x |- f x = (g:'a->'b) x                      
let th5 = mk_abs_rule x th4                            // 5  !x. f x = g x |- (\x. f x) = (\x. (g:'a->'b) x)          
let th6 = parse_term(@"\x. (g:'a->'b) x") |> eta_conv  // 6                |- (\x. (g:'a->'b) x) = g                  
let th7 = [th2; th5; th6] |> list_trans_rule           // 7  !x. f x = g x |- f = (g:'a->'b)                          
let th8 = parse_term(@"(f:'a->'b)=g") |> assume_rule   // 8          f = g |- f = (g:'a->'b)                          
let th9 = mk_comb1_rule th8 x                          // 9          f = g |- f x = (g:'a->'b) x                      
let th10 = gen_rule x th9                              // 10         f = g |- !x. f x = (g:'a->'b) x                  
let th11 = deduct_antisym_rule th7 th10                // 11               |- f = (g:'a->'b) <=> (!x. f x = g x)      
let th = list_gen_rule [f;g] th11                      //                  |- !(f:'a->'b) g. f = g <=> (!x. f x = g x)

(**
$\scriptsize{\dfrac
    {
        \dfrac
            {
                \dfrac
                    {
                        \dfrac
                            {
                                \dfrac
                                    {}
                                    {(1) \vdash (\lambda x. (f:\alpha \rightarrow \beta)\ x) = f}
                                    \textsf{eta_conv}}
                            {(2) \vdash (f:\alpha \rightarrow \beta) = (\lambda x. f\ x)}
                            \textsf{sym_rule}
                    \qquad 
                        \dfrac
                            {
                                \dfrac
                                    {\dfrac{}{(3) \forall x. f\ x = g\ x \vdash \forall x. f\ x = (g:\alpha \rightarrow \beta)\ x}\textsf{assume_rule}}
                                    {(4)\forall x. f\ x = g\ x \vdash f\ x = (g:\alpha \rightarrow \beta)\ x}
                                    \textsf{spec_rule}
                            }
                            {(5) \forall x. f\ x = g\ x \vdash (\lambda x. f\ x) = (\lambda x. (g:\alpha \rightarrow \beta)\ x)}\textsf{mk_abs_rule}
                    \qquad 
                        \dfrac{}{(6) \vdash (\lambda x. (g:\alpha \rightarrow \beta)\ x) = g}\textsf{eta_conv}
                    }
                    {(7) \forall x.\ f\ x = g\ x \vdash f = (g:\alpha \rightarrow \beta)}\textsf{list_trans_rule}
                \qquad 
                \dfrac
                    {
                        \dfrac
                            {
                                \dfrac{}{(8) f = g \vdash f = (g:\alpha \rightarrow \beta)}\textsf{assume_rule}
                            }
                            {(9) f = g \vdash f\ x = (g:\alpha \rightarrow \beta)\ x}\textsf{mk_comb1_rule}
                    }
                    {(10) f = g \vdash \forall x. f\ x = (g: \alpha \rightarrow \beta)\ x}\textsf{gen_rule}
            }
            {
                (11) \vdash f = g\ \leftrightarrow\ (\forall x.\ f\ x = g\ x)
            }\textsf{deduct_antisym_rule}
    }
      {(th) \vdash \forall (f:\alpha \rightarrow \beta)\ g.\ f = g\ \leftrightarrow\ (\forall x.\ f\ x = g\ x)}
      \textsf{list_gen_rule}}$
*)

(**
Logica Predicativa
------------

**truth\_thm**

`true` &egrave; sempre dimostrato

*)

truth_thm
// |- true

true_def                                            // |- true <=> (\(p:bool). p) = (\p. p)
let tt1 = sym_rule true_def                         // |- (\(p:bool). p) = (\p. p) <=> true
let tt2 = refl_conv (parse_term(@"\(p:bool).p"))    // |- (\(p:bool). p) = (\p. p)
let tt3 = eq_mp_rule tt1 tt2                        // |- true

(**
$\scriptsize{
\dfrac
    {
        \dfrac
            {\dfrac{}{\vdash \top \Leftrightarrow (\lambda(p:bool). p) = (\lambda p. p)}\textsf{true_def}}
            {\vdash (\lambda (p:bool).\ p) = (\lambda p. p) \Leftrightarrow \top}\textsf{sym_rule}
        \qquad
        \dfrac{}{\vdash (\lambda (p:bool).\ p) = (\lambda p. p)}\textsf{refl_conv}
    }
    {\vdash \top}\textsf{eq_mp_rule}
}$

**excluded\_middle\_thm**

Per qualsiasi proposizione, o essa &egrave; dimostrabile o lo &egrave; la sua negazione

*)

excluded_middle_thm
// |- !p. p \/ ~ p

let emt1 = assume_rule p                           //                                  p |- p
let emt2 = disj1_rule emt1 (mk_not p)              //                                  p |- p \/ ~ p
let emt3 = "false" |> parse_term |> refl_conv      //                                    |- false <=> false
let emt4 = disj1_rule emt3 p                       //                                    |- (false <=> false) \/ p
let emt5 =                                                                            
    exists_rule                                                                       
        ((parse_term(@"?x. (x <=> false) \/ p")),                                     
            (parse_term(@"false"))) emt4           //                                    |- ?x. (x <=> false) \/ p
let emt6 = select_rule emt5                        //                                    |- ((@x. (x <=> false) \/ p) <=> false) \/ p
let emt7 = refl_conv (parse_term(@"true"))         //                                    |- true <=> true
let emt8 = disj1_rule emt7 p                       //                                    |- (true <=> true) \/ p
let emt9 =                                                                            
    exists_rule                                                                       
        ((parse_term(@"?x. (x <=> true) \/ p")),                                      
            (parse_term(@"true"))) emt8            //                                    |- ?x. (x <=> true) \/ p
let emt10 = select_rule emt9                       //                                    |- ((@x. (x <=> true) \/ p) <=> true) \/ p
let emt11 = 
    assume_rule 
        (parse_term(@"(@x. (x <=> true) \/ p) 
            <=> true"))                            //   (@x. (x <=> true) \/ p) <=> true |- (@x. (x <=> true) \/ p) <=> true
let emt12 = 
    assume_rule 
        (parse_term(@"(@x. (x <=> false) \/ p) 
            <=> false"))                           // (@x. (x <=> false) \/ p) <=> false |- (@x. (x <=> false) \/ p) <=> false
let emt13 = mk_eq_rule emt11 emt12                 // (@x. (x <=> true) \/ p) <=> true, 
                                                   // (@x. (x <=> false) \/ p) <=> false 
                                                   //                                    |- ((@x. (x <=> true) \/ p) 
                                                   //                                         <=> (@x. (x <=> false) \/ p)) 
                                                   //                                       <=> (true <=> false)
let emt14 = 
    disj2_rule (parse_term(@"x <=> true")) emt1    //                                  p |- (x <=> true) \/ p
let emt15 = 
    disj2_rule (parse_term(@"x <=> false")) emt1   //                                  p |- (x <=> false) \/ p
let emt16 = deduct_antisym_rule emt14 emt15        //                                  p |- (x <=> true) \/ p <=> (x <=> false) \/ p
let emt17 = 
    mk_select_rule 
        (parse_term(@"x:bool")) emt16              //                                  p |- (@x. (x <=> true) \/ p) <=> (@x. (x <=> false) \/ p)
let emt18 = eq_mp_rule emt13 emt17                 // (@x. (x <=> true) \/ p) <=> true, 
                                                   // (@x. (x <=> false) \/ p) <=> false,
                                                   // p
                                                   //                                    |- true <=> false
let emt19 = eq_mp_rule emt18 truth_thm             // (@x. (x <=> true) \/ p) <=> true, 
                                                   // (@x. (x <=> false) \/ p) <=> false,
                                                   // p
                                                   //                                    |- false
let emt20 = disch_rule p emt19                     // (@x. (x <=> true) \/ p) <=> true, 
                                                   // (@x. (x <=> false) \/ p) <=> false
                                                   //                                    |- p ==> false
let emt21 = not_intro_rule emt20                   // (@x. (x <=> true) \/ p) <=> true, 
                                                   // (@x. (x <=> false) \/ p) <=> false
                                                   //                                    |- ~ p
let emt22 = disj2_rule p emt21                     // (@x. (x <=> true) \/ p) <=> true, 
                                                   // (@x. (x <=> false) \/ p) <=> false
                                                   //                                    |- p \/ ~ p
let emt23 = disj_cases_rule emt10 emt22 emt2       // (@x. (x <=> false) \/ p) <=> false |- p \/ ~ p
let emt24 = disj_cases_rule emt6 emt23 emt2        //                                    |- p \/ ~ p

(**
$\scriptsize{
\dfrac
    {
        \dfrac
            {
                \dfrac
                    {
                        \dfrac
                            {
                                \dfrac
                                    {}
                                    {(3) \vdash \bot \Leftrightarrow \bot}
                                    \textsf{refl_conv}
                            }
                            {(4) \vdash (\bot \Leftrightarrow \bot) \vee p}
                            \textsf{disj1_rule}
                    }
                    {(5) \vdash \exists x. (x \Leftrightarrow \bot) \vee p}
                    \textsf{exists_rule}
            }
            {(6) \vdash ((\epsilon x. (x \Leftrightarrow \bot) \vee p)\Leftrightarrow \bot) \vee p}
            \textsf{select_rule}
        \qquad 
        \dfrac
            {
                \dfrac
                    {
                        \dfrac
                            {
                                \dfrac
                                    {
                                        \dfrac
                                            {}
                                            {(7) (\top \Leftrightarrow \top)}
                                            \textsf{refl_conv}
                                    }
                                    {(8) (\top \Leftrightarrow \top) \vee p}
                                    \textsf{disj1_rule}
                            }
                            {(9) \exists x. (x \Leftrightarrow \top) \vee p}
                            \textsf{exists_rule}
                    }
                    {(10) \vdash ((\epsilon x. (x \Leftrightarrow \top) \vee p) \Leftrightarrow \top) \vee p}
                    \textsf{select_rule}
                \qquad
                    \dfrac
                    {
                        \dfrac
                        {
                            \dfrac
                            {
                                \dfrac
                                {
                                    \dfrac
                                        {
                                            \dfrac
                                            {\dots}
                                            {(13) (\epsilon x. (x \Leftrightarrow \bot) \vee p) \Leftrightarrow \bot }
                                            \textsf{mk_eq_rule}
                                            \qquad
                                            \dfrac
                                                {\dots}
                                                {(17) p \vdash (\epsilon x. (x \Leftrightarrow \top) \vee p) \Leftrightarrow (\epsilon x. (x \Leftrightarrow \bot) \vee p)}
                                                \textsf{mk_select_rule}
                                        }
                                        {(18) (\epsilon x. (x \Leftrightarrow \top) \vee p) \Leftrightarrow \top, (\epsilon x. (x \Leftrightarrow \bot) \vee p) \Leftrightarrow, p \bot \vdash \top \Leftrightarrow \bot}
                                        \textsf{eq_mp_rule}
                                    \qquad
                                    (truth\_tm) \vdash \top
                                }
                                {(19) (\epsilon x. (x \Leftrightarrow \top) \vee p) \Leftrightarrow \top, (\epsilon x. (x \Leftrightarrow \bot) \vee p) \Leftrightarrow, p \bot \vdash \bot}
                                \textsf{eq_mp_rule}
                            }
                            {(20) (\epsilon x. (x \Leftrightarrow \top) \vee p) \Leftrightarrow \top, (\epsilon x. (x \Leftrightarrow \bot) \vee p) \Leftrightarrow \bot \vdash p \rightarrow \bot}
                            \textsf{disch_rule}
                        }
                        {(21) (\epsilon x. (x \Leftrightarrow \top) \vee p) \Leftrightarrow \top, (\epsilon x. (x \Leftrightarrow \bot) \vee p) \Leftrightarrow \bot \vdash \neg p}
                        \textsf{not_intro_rule}
                    }
                    {(22) (\epsilon x. (x \Leftrightarrow \top) \vee p) \Leftrightarrow \top, (\epsilon x. (x \Leftrightarrow \bot) \vee p) \Leftrightarrow \bot \vdash p \vee \neg p}
                    \textsf{disj2_rule}
                \qquad
                \dfrac
                {
                    \dfrac
                        {}
                        {(1) p \vdash p}
                        \textsf{assume_rule}
                }
                {(2) p \vdash p \vee \neg p}
                \textsf{disj1_rule}
            }
            {(23) (\epsilon x. (x \Leftrightarrow \bot) \vee p) \Leftrightarrow \bot \vdash p \vee \neg p}
            \textsf{disj_cases_rule}
        \qquad
        \dfrac
            {
                \dfrac
                    {}
                    {(1) p \vdash p}
                    \textsf{assume_rule}
            }
            {(2) p \vdash p \vee \neg p}
            \textsf{disj1_rule}
    }
    {\vdash p \vee \neg p}
    \textsf{disj_cases_rule}
}
$
*)




(**                                                
**bool\_cases\_thm**
*)

bool_cases_thm
// |- !p. (p <=> true) \/ (p <=> false)

let p = mk_var ("p",bool_ty)
let tm1 = spec_rule p excluded_middle_thm                   //     |- p \/ ~ p
let tm2 = eqt_intro_rule (assume_rule p)                    //   p |- p <=> true
let tm3 = disj1_rule tm2 (parse_term(@"p <=> false"))       //   p |- (p <=> true) \/ (p <=> false)
let tm4 = eqf_intro_rule (assume_rule (parse_term(@"~ p"))) // ~ p |- p <=> false
let tm5 = disj2_rule (parse_term(@"p <=> true")) tm4        // ~ p |- (p <=> true) \/ (p <=> false)
let tm = disj_cases_rule tm1 tm3 tm5                        //     |- (p <=> true) \/ (p <=> false)

(**

$\scriptsize{
\dfrac
    {
        \dfrac{}{\vdash p \vee \neg p}\textsf{excluded_middle_thm}
        \qquad
        p \vdash (p \leftrightarrow \top) \vee (p \leftrightarrow \bot)
        \qquad
        \neg p \vdash (p \leftrightarrow \top) \vee (p \leftrightarrow \bot)
    }
    {\vdash p \leftrightarrow \top \vee p \leftrightarrow \bot}\textsf{disj_cases_rule}
}$
*)

cond_false_thm
// |- !(t1:'a) t2. (if false then t1 else t2) = t2

cond_idem_thm
// |- !p (t:'a). (if p then t else t) = t

cond_not_thm
// |- !p (t1:'a) t2. (if (~ p) then t1 else t2) = (if p then t2 else t1)

cond_true_thm
// |- !(t1:'a) t2. (if true then t1 else t2) = t1

//conj_absorb_disj_thm
//   |- !p q. p /\ (p \/ q) <=> p

//conj_assoc_thm
//   |- !p q r. p /\ (q /\ r) <=> (p /\ q) /\ r

//conj_comm_thm
//   |- !p q. p /\ q <=> q /\ p

//conj_contr_thm
//   |- !p. p /\ ~ p <=> false

//conj_dist_left_disj_thm
//   |- !p q r. (p \/ q) /\ r <=> (p /\ r) \/ (q /\ r)

//conj_dist_right_disj_thm
//   |- !p q r. p /\ (q \/ r) <=> (p /\ q) \/ (p /\ r)

//conj_id_thm
//   |- !p. p /\ true <=> p

//conj_idem_thm
//   |- !p. p /\ p <=> p

//conj_zero_thm
//   |- !p. p /\ false <=> false

//disj_absorb_conj_thm
//   |- !p q. p \/ (p /\ q) <=> p

//disj_assoc_thm
//   |- !p q r. p \/ (q \/ r) <=> (p \/ q) \/ r

//disj_comm_thm
//   |- !p q. p \/ q <=> q \/ p

//disj_dist_left_conj_thm
//   |- !p q r. (p /\ q) \/ r <=> (p \/ r) /\ (q \/ r)

//disj_dist_right_conj_thm
//   |- !p q r. p \/ (q /\ r) <=> (p \/ q) /\ (p \/ r)

//disj_id_thm
//   |- !p. p \/ false <=> p

//disj_idem_thm
//   |- !p. p \/ p <=> p

//disj_zero_thm
//   |- !p. p \/ true <=> true



//exists_dist_disj_thm
//   |- !(P:'a->bool) Q. (?x. P x \/ Q x) <=> (?x. P x) \/ (?x. Q x)

//exists_null_thm
//   |- !t. (?(x:'a). t) <=> t

//exists_one_point_thm
//   |- !(P:'a->bool) a. (?x. x = a /\ P x) <=> P a

//exists_value_thm
//   |- !(x:'a). ?y. y = x

//forall_dist_conj_thm
//   |- !(P:'a->bool) Q. (!x. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)

//forall_null_thm
//   |- !t. (!(x:'a). t) <=> t

//forall_one_point_thm
//   |- !(P:'a->bool) a. (!x. x = a ==> P x) <=> P a

//imp_alt_def_thm
//   |- $==> = (\p q. p /\ q <=> p)

//imp_disj_thm
//   |- !p q. (p ==> q) <=> (~ p \/ q)

//imp_dist_left_disj_thm
//   |- !p q r. (p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)

//imp_dist_right_conj_thm
//   |- !p q r. (p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)

//imp_imp_thm
//   |- !p q r. (p ==> q ==> r) <=> (p /\ q ==> r)

//imp_left_id_thm
//   |- !p. (true ==> p) <=> p

//imp_left_zero_thm
//   |- !p. false ==> p

//imp_refl_thm
//   |- !p. p ==> p

//imp_right_zero_thm
//   |- !p. p ==> true

//not_dist_conj_thm
//   |- !p q. ~ (p /\ q) <=> ~ p \/ ~ q

//not_dist_disj_thm
//   |- !p q. ~ (p \/ q) <=> ~ p /\ ~ q

//not_dist_exists_thm
//   |- !(P:'a->bool). ~ (?x. P x) <=> (!x. ~ P x)

//not_dist_forall_thm
//   |- !(P:'a->bool). ~ (!x. P x) <=> (?x. ~ P x)

//not_dneg_thm
//   |- !p. ~ ~ p <=> p

//not_false_thm
//   |- ~ false <=> true

//not_true_thm
//   |- ~ true <=> false

//select_eq_thm
//   |- !(a:'a). (@x. x = a) = a

//skolem_thm
//   |- !(P:'a->'b->bool). (!x. ?y. P x y) <=> (?f. !x. P x (f x))

//true_not_eq_false_thm
//   |- ~ (true <=> false)



//uexists_thm1
//   |- !(P:'a->bool). (?!x. P x) <=> (?x. P x /\ (!y. P y ==> y = x))

//uexists_thm2
//   |- !(P:'a->bool). (?!x. P x) <=> (?x. !y. P y <=> x = y)

//uexists_thm3
//   |- !(P:'a->bool). (?!x. P x)
//                     <=> (?x. P x) /\ (!x' x''. P x' /\ P x'' ==> x' = x'')

//uexists_one_point_thm
//   |- !(P:'a->bool) a. (?!x. x = a /\ P x) <=> P a

//unique_skolem_thm : thm =
//   |- !(P:'a->'b->bool). (!x. ?!y. P x y) <=> (?f. !x y. P x y <=> f x = y)


(***hide***)
//********************************************************************************

//PAIRS

//fst_snd_thm
//   |- !(p:'a#'b). (FST p, SND p) = p

//fst_thm
//   |- !(x:'a) (y:'b). FST (x,y) = x

//pair_eq_thm
//   |- !(x:'a) (y:'b) u v. (x,y) = (u,v) <=> x = u /\ y = v

//pair_surjective_thm
//   |- !(p:'a#'b). ?x y. p = (x,y)

//snd_thm
//   |- !(x:'a) (y:'b). SND (x,y) = y

//********************************************************************************

//INDIVIDUALS

//ind_suc_injective_thm
//   |- !i j. IND_SUC i = IND_SUC j <=> i = j

//ind_suc_not_zero_thm
//   |- !i. ~ (IND_SUC i = IND_ZERO)

//********************************************************************************

//NATURAL NUMBERS

//add_assoc_thm
//   |- !l m n. l + (m + n) = (l + m) + n

//add_comm_thm
//   |- !m n. m + n = n + m

//add_dist_left_suc_thm
//   |- !m n. (SUC m) + n = SUC (m + n)

//add_dist_right_suc_thm
//   |- !m n. m + (SUC n) = SUC (m + n)

//add_eq_cancel_thm
//   |- !l m n. l + n = m + n <=> l = m

//add_eq_zero_thm
//   |- !m n. m + n = 0 <=> m = 0 /\ n = 0

//add_id_thm
//   |- !n. n + 0 = n

//add_le_cancel_thm
//   |- !l m n. l + n <= m + n <=> l <= m

//add_lt_cancel_thm
//   |- !l m n. l + n < m + n <=> l < m

//add_sub_cancel_thm
//   |- !m n. (m + n) - n = m

//even_suc_thm
//   |- !n. EVEN (SUC n) <=> ~ EVEN n

//exp_dist_right_add_thm
//   |- !l m n. l EXP (m + n) = (l EXP m) * (l EXP n)

//exp_dist_right_suc_thm
//   |- !m n. m EXP (SUC n) = m * m EXP n

//exp_right_id_thm
//   |- !n. n EXP 1 = n

//exp_right_zero_thm
//   |- !n. n EXP 0 = 1

//le_antisym_thm
//   |- !m n. m <= n /\ n <= m ==> m = n

//le_cases_thm
//   |- !m n. m <= n <=> m < n \/ m = n

//le_refl_thm
//   |- !n. n <= n

//le_trans_thm
//   |- !l m n. l <= m /\ m <= n ==> l <= n

//le_zero_thm
//   |- !n. n <= 0 <=> n = 0

//lt_asym_thm
//   |- !m n. ~ (m < n /\ n < m)

//lt_irrefl_thm
//   |- !n. ~ (n < n)

//lt_suc_cases_thm
//   |- !m n. m < SUC n <=> m = n \/ m < n

//lt_suc_le_thm
//   |- !m n. m < SUC n <=> m <= n

//lt_suc_thm
//   |- !n. n < SUC n

//lt_trans_thm
//   |- !l m n. l < m /\ m < n ==> l < n

//lt_zero_cases_thm
//   |- !n. n = 0 \/ 0 < n

//mult_assoc_thm
//   |- !l m n. l * (m * n) = (l * m) * n

//mult_comm_thm
//   |- !m n. m * n = n * m

//mult_dist_left_add_thm
//   |- !l m n. (l + m) * n = l * n + m * n

//mult_dist_left_suc_thm
//   |- !m n. (SUC m) * n = n + m * n

//mult_dist_right_add_thm
//   |- !l m n. l * (m + n) = l * m + l * n

//mult_dist_right_suc_thm
//   |- !m n. m * SUC n = m + (m * n)

//mult_eq_cancel_thm
//   |- !l m n. ~ (l = 0) ==> (l * m = l * n <=> m = n)

//mult_eq_zero_thm
//   |- !m n. m * n = 0 <=> m = 0 \/ n = 0

//mult_id_thm
//   |- !n. n * 1 = n

//mult_le_cancel_thm
//   |- !l m n. ~ (l = 0) ==> (l * m <= l * n <=> m <= n)

//mult_lt_cancel_thm
//   |- !l m n. ~ (l = 0) ==> (l * m < l * n <=> m < n)

//mult_zero_thm
//   |- !n. n * 0 = 0

//nat_cases_thm
//   |- !n. n = 0 \/ (?m. n = SUC m)

//nat_induction_thm
//   |- !P. P 0 /\ (!n. P n ==> P (SUC n)) ==> (!n. P n)

//nat_recursion_thm
//   |- !(e1:'a) e2. ?F. F 0 = e1 /\ (!n. F (SUC n) = e2 (F n) n)

//not_lt_cases_thm
//   |- !m n. ~ (m < n) <=> n = m \/ n < m

//not_lt_zero_thm
//   |- !n. ~ (n < 0)

//odd_suc_thm
//   |- !n. ODD (SUC n) <=> ~ ODD n

//one_not_zero_thm
//   |- ~ (1 = 0)

//one_odd_thm
//   |- ODD 1

//pre_suc_thm
//   |- !n. PRE (SUC n) = n

//pre_zero_thm
//   |- PRE 0 = 0

//sub_cancel_thm
//   |- !n. n - n = 0

//sub_dist_right_suc_thm
//   |- !m n. m - SUC n = PRE (m - n)

//sub_floor_thm
//   |- !m n. m <= n ==> m - n = 0

//sub_right_id_thm
//   |- !n. n - 0 = n

//suc_add_thm
//   |- !n. SUC n = n + 1

//suc_injective_thm
//   |- !m n. SUC m = SUC n <=> m = n

//suc_le_cancel_thm
//   |- !m n. SUC m <= SUC n <=> m <= n

//suc_le_lt_thm
//   |- !m n. SUC m <= n <=> m < n

//suc_lt_cancel_thm
//   |- !m n. SUC m < SUC n <=> m < n

//suc_not_zero_thm
//   |- !n. ~ (SUC n = 0)

//suc_one_thm
//   |- SUC 1 = 2

//suc_sub_suc_thm
//   |- !m n. SUC m - SUC n = m - n

//suc_twice_odd_thm
//   |- !n. ODD (SUC (2 * n))

//suc_zero_thm
//   |- SUC 0 = 1

//twice_even_thm
//   |- !n. EVEN (2 * n)

//twice_thm
//   |- !n. 2 * n = n + n

//two_not_zero_thm
//   |- ~ (2 = 0)

//zero_even_thm
//   |- EVEN 0

//zero_le_thm
//   |- !n. 0 <= n

//zero_lt_suc_thm
//   |- !n. 0 < SUC n

//zero_lt_thm
//   |- !n. 0 < n <=> ~ (n = 0)

//zero_not_odd_thm
//   |- ~ ODD 0

//********************************************************************************
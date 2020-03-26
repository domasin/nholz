(**
Terzo escluso
=====================

$\vdash \forall p.\ p \vee \neg p$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
BoolAlg.load
BoolClass.load
(***unhide***)

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
let excluded_middle = gen_rule p emt24             //                                    |- !p. p \/ ~ p

(**
$\scriptsize{
\dfrac
{
    p
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
                                                {
                                                    (11) (\epsilon x. (x \Leftrightarrow \top) \vee p) \Leftrightarrow \top \vdash (\epsilon x. (x \Leftrightarrow \top) \vee p) \Leftrightarrow \top
                                                    \qquad
                                                    (12) (\epsilon x.\ (x \Leftrightarrow \bot) \vee p) \Leftrightarrow \bot \vdash (x \Leftrightarrow \bot) \vee p) \Leftrightarrow \bot}
                                                {
                                                    (13) (\epsilon x. (x \Leftrightarrow \top) \vee p) \Leftrightarrow \top,
                                                    (\epsilon x. (x \Leftrightarrow \bot) \vee p) \Leftrightarrow \bot 
                                                    \vdash ((\epsilon x. (x \Leftrightarrow \top) \vee p) \Leftrightarrow (\epsilon x. (x \Leftrightarrow \bot) \vee p))  \Leftrightarrow (\top \Leftrightarrow \bot)
                                                }
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
    {\vdash \forall p.\ p \vee \neg p}
    \textsf{ gen_rule}
}
$
*)
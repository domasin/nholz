(**
Disj Id
=============

$\vdash \forall p.\ p \vee \bot \Leftrightarrow p$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

disj_id_thm
// |- !p. p \/ false <=> p

let p = "p:bool" |> parse_term
let th1 = assume_rule p                                //          p |- p
let th2 = disj1_rule th1 (parse_term(@"false"))        //          p |- p \/ false    
let th3 = assume_rule (parse_term(@"p \/ false"))      // p \/ false |- p \/ false
let th4 = assume_rule (parse_term(@"false"))           //      false |- false
let th5 = contr_rule p th4                             //      false |- p
let th6 = disj_cases_rule th3 th1 th5                  // p \/ false |- p
let th7 = deduct_antisym_rule th2 th6                  //            |- p \/ false <=> p
let th8 = gen_rule p th7                               //            |- !p. p \/ false <=> p

(***hide***)
//let th1 = assume_rule_tr p                       
//let th2 = disj1_rule_tr th1 (parse_term(@"false"))             
//let th3 = assume_rule_tr (parse_term(@"p \/ false"))    
//let th4 = assume_rule_tr (parse_term(@"false"))
//let th5 = contr_rule_tr p th4
//let th6 = disj_cases_rule_tr th3 th1 th5
//let th7 = deduct_antisym_rule_tr th2 th6
//let th8 = gen_rule_tr p th7
(***unhide***)

(**
$
\small{     
\dfrac
    {p:bool
    \qquad
    \dfrac
        {\dfrac
            {\dfrac
                {p:bool}
                {p\ \vdash\ p}
                \textsf{ assume_rule}
            \qquad
            \bot}
            {p\ \vdash\ p\ \vee\ \bot}
            \textsf{ disj1_rule}
        \qquad
        \dfrac
            {\dfrac
                {p\ \vee\ \bot}
                {p\ \vee\ \bot\ \vdash\ p\ \vee\ \bot}
                \textsf{ assume_rule}
            \qquad
            \dfrac
                {p:bool}
                {p\ \vdash\ p}
                \textsf{ assume_rule}
            \qquad
            \dfrac
                {p:bool
                \qquad
                \dfrac
                    {\bot}
                    {\bot\ \vdash\ \bot}
                    \textsf{ assume_rule}}
                {\bot\ \vdash\ p}
                \textsf{ contr_rule}}
            {p\ \vee\ \bot\ \vdash\ p}
            \textsf{ disj_cases_rule}}
        {\vdash\ p\ \vee\ \bot\ \Leftrightarrow\ p}
        \textsf{ deduct_antisym_rule}}
    {\vdash\ \forall\ p.\ p\ \vee\ \bot\ \Leftrightarrow\ p}
    \textsf{ gen_rule} }
$
*)
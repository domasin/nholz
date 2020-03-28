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

(***hide***)
let th1 = assume_rule_tr p
let th2 = disj1_rule_tr th1 (mk_not p)
let th3 = "false" |> parse_term |> refl_conv_tr
let th4 = disj1_rule_tr th3 p 
let th5 =                                                                            
    exists_rule_tr                                                                      
        ((parse_term(@"?x. (x <=> false) \/ p")),                                     
            (parse_term(@"false"))) th4  
let th6 = select_rule_tr th5
let th7 = refl_conv_tr (parse_term(@"true")) 
let th8 = disj1_rule_tr th7 p
let th9 =                                                                            
    exists_rule_tr                                                                       
        ((parse_term(@"?x. (x <=> true) \/ p")),                                      
            (parse_term(@"true"))) th8  
let th10 = select_rule_tr th9
let th11 = 
    assume_rule_tr
        (parse_term(@"(@x. (x <=> true) \/ p) 
            <=> true"))    
let th12 = 
    assume_rule_tr
        (parse_term(@"(@x. (x <=> false) \/ p) 
            <=> false"))  
let th13 = mk_eq_rule_tr th11 th12
let th14 = 
    disj2_rule_tr (parse_term(@"x <=> true")) th1
let th15 = 
    disj2_rule_tr (parse_term(@"x <=> false")) th1
let th16 = deduct_antisym_rule_tr th14 th15
let th17 = 
    mk_select_rule_tr 
        (parse_term(@"x:bool")) th16 
let th18 = eq_mp_rule_tr th13 th17
let truth_thm_gr = (truth_thm, mkGraph (Th truth_thm, "truth\_thm") [])
let th19 = eq_mp_rule_tr th18 truth_thm_gr
let th20 = disch_rule_tr p th19
let th21 = not_intro_rule_tr th20
let th22 = disj2_rule_tr p th21
let th23 = disj_cases_rule_tr th10 th22 th2
let th24 = disj_cases_rule_tr th6 th23 th2
let th25 = gen_rule_tr p th24

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
				{\exists x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p
				\qquad
				\bot
				\qquad
				\dfrac
					{\dfrac
						{\bot}
						{\vdash\ \bot\ \Leftrightarrow\ \bot}
						\textsf{ refl_conv}
					\qquad
					p:bool}
					{\vdash\ (\bot\ \Leftrightarrow\ \bot)\ \vee\ p}
					\textsf{ disj1_rule}}
				{\vdash\ \exists x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p}
				\textsf{ exists_rule}}
			{\vdash\ ((\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)\ \Leftrightarrow\ \bot)\ \vee\ p}
			\textsf{ select_rule}
		\qquad
		\dfrac
			{\dfrac
				{\dfrac
					{\exists x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p
					\qquad
					\top
					\qquad
					\dfrac
						{\dfrac
							{\top}
							{\vdash\ \top\ \Leftrightarrow\ \top}
							\textsf{ refl_conv}
						\qquad
						p:bool}
						{\vdash\ (\top\ \Leftrightarrow\ \top)\ \vee\ p}
						\textsf{ disj1_rule}}
					{\vdash\ \exists x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p}
					\textsf{ exists_rule}}
				{\vdash\ ((\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ \top)\ \vee\ p}
				\textsf{ select_rule}
			\qquad
			\dfrac
				{p:bool
				\qquad
				\dfrac
					{\dfrac
						{p:bool
						\qquad
						\dfrac
							{\dfrac
								{\dfrac
									{\dfrac
										{(\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ \top}
										{(\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ \top\ \vdash\ (\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ \top}
										\textsf{ assume_rule}
									\qquad
									\dfrac
										{(\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)\ \Leftrightarrow\ \bot}
										{(\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)\ \Leftrightarrow\ \bot\ \vdash\ (\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)\ \Leftrightarrow\ \bot}
										\textsf{ assume_rule}}
									{(\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ \top,\ (\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)\ \Leftrightarrow\ \bot\ \vdash\ ((\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ (\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p))\ \Leftrightarrow\ (\top\ \Leftrightarrow\ \bot)}
									\textsf{ mk_eq_rule}
								\qquad
								\dfrac
									{x:bool
									\qquad
									\dfrac
										{\dfrac
											{x\ \Leftrightarrow\ \top
											\qquad
											\dfrac
												{p:bool}
												{p\ \vdash\ p}
												\textsf{ assume_rule}}
											{p\ \vdash\ (x\ \Leftrightarrow\ \top)\ \vee\ p}
											\textsf{ disj2_rule}
										\qquad
										\dfrac
											{x\ \Leftrightarrow\ \bot
											\qquad
											\dfrac
												{p:bool}
												{p\ \vdash\ p}
												\textsf{ assume_rule}}
											{p\ \vdash\ (x\ \Leftrightarrow\ \bot)\ \vee\ p}
											\textsf{ disj2_rule}}
										{p\ \vdash\ (x\ \Leftrightarrow\ \top)\ \vee\ p\ \Leftrightarrow\ (x\ \Leftrightarrow\ \bot)\ \vee\ p}
										\textsf{ deduct_antisym_rule}}
									{p\ \vdash\ (\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ (\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)}
									\textsf{ mk_select_rule}}
								{(\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ \top,\ (\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)\ \Leftrightarrow\ \bot,\ p\ \vdash\ \top\ \Leftrightarrow\ \bot}
								\textsf{ eq_mp_rule}
							\qquad
							\vdash\ \top}
							{(\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ \top,\ (\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)\ \Leftrightarrow\ \bot,\ p\ \vdash\ \bot}
							\textsf{ eq_mp_rule}}
						{(\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ \top,\ (\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)\ \Leftrightarrow\ \bot\ \vdash\ p\ \Rightarrow\ \bot}
						\textsf{ disch_rule}}
					{(\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ \top,\ (\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)\ \Leftrightarrow\ \bot\ \vdash\ \neg\ p}
					\textsf{ not_intro_rule}}
				{(\epsilon x.\ (x\ \Leftrightarrow\ \top)\ \vee\ p)\ \Leftrightarrow\ \top,\ (\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)\ \Leftrightarrow\ \bot\ \vdash\ p\ \vee\ \neg\ p}
				\textsf{ disj2_rule}
			\qquad
			\dfrac
				{\dfrac
					{p:bool}
					{p\ \vdash\ p}
					\textsf{ assume_rule}
				\qquad
				\neg\ p}
				{p\ \vdash\ p\ \vee\ \neg\ p}
				\textsf{ disj1_rule}}
			{(\epsilon x.\ (x\ \Leftrightarrow\ \bot)\ \vee\ p)\ \Leftrightarrow\ \bot\ \vdash\ p\ \vee\ \neg\ p}
			\textsf{ disj_cases_rule}
		\qquad
		\dfrac
			{\dfrac
				{p:bool}
				{p\ \vdash\ p}
				\textsf{ assume_rule}
			\qquad
			\neg\ p}
			{p\ \vdash\ p\ \vee\ \neg\ p}
			\textsf{ disj1_rule}}
		{\vdash\ p\ \vee\ \neg\ p}
		\textsf{ disj_cases_rule}}
	{\vdash\ \forall\ p.\ p\ \vee\ \neg\ p}
	\textsf{ gen_rule} }
$
*)
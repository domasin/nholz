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
BoolAlg.load
BoolClass.load
Pair.load
Ind.load
Nat.load
NatNumrl.load

// Types
prim_get_all_tyconsts()

// Signature
get_all_consts()

// Axioms
get_all_const_definitions()
get_all_axioms()

// Theorems
get_all_lemmas()
get_all_thms ()

// Other stored items
step_total () 
get_all_const_specifications ()
!the_enum_brackets 
get_all_enum_info ()
get_all_fixities()
get_all_fun_definitions ()
get_language_level_mode ()
!the_relative_step_start 
get_all_tyconst_definition_info ()
get_type_annotation_mode ()
get_all_type_bijections () 
get_all_type_fixities()
get_tyvar_marking_mode ()
get_var_marking_mode ()

// Sample dedection

let t1 = (contr_rule (parse_term(@"~ true")) (assume_rule (parse_term(@"false"))))
let t2 = (eqf_intro_rule (assume_rule (parse_term(@"~ true"))))
let t3 = eq_mp_rule t2 truth_thm
let t4 = deduct_antisym_rule t1 t3

let th1 = assume_rule (parse_term(@"p ==> q"))
let th2 = mp_rule th1 (assume_rule (parse_term(@"p:bool"))) 
let th3 = add_asm_rule (parse_term(@"~ q:bool")) th2
let th4 = deduct_contrapos_rule (parse_term(@"p:bool")) th3
let th5 = prim_disch_rule  (parse_term(@"~ q:bool")) th4 // p ==> q |- ~ q ==> ~ p

let th6 = assume_rule (parse_term(@"~ q ==> ~ p"))
let th7 = add_asm_rule (parse_term(@"p:bool")) th6
let th8 = mp_rule th7 (assume_rule (parse_term(@"~ q")))
let th9 = not_elim_rule th8
let th10 = undisch_rule th9
let th11 = ccontr_rule  (parse_term(@"q:bool")) th10
let th12 = disch_rule  (parse_term(@"p:bool")) th11
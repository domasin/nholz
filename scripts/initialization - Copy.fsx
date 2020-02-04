#I "./bin/debug/netstandard2.0"
#r "nholz.dll"
open NHolz

fsi.AddPrinter print_type
fsi.AddPrinter print_qtype
fsi.AddPrinter print_term
fsi.AddPrinter print_qterm
fsi.AddPrinter print_thm

CoreThry.load
//Equal.load

//// This forces evaluation of modules

//bool_ty;;               //CoreThry
//let_def;;               //Equal
//false_def;;             //Bool
//not_true_thm;;          //BoolAlg
//excluded_middle_thm;;   //BoolClass
//mk_pair_rep_def;;       //Pair
//ind_ty;;                //Ind
//is_nat_rep_def;;        //Nat
//numeral_def;;           //NatNumrl
//add_def;;               //NatArith
//lt_def;;                //NatRel

// Struttura di tipo
prim_get_all_tyconsts()

// Firma
get_all_consts()

// Assiomi
get_all_const_definitions()
get_all_axioms()

// Teoremi
get_all_lemmas()
get_all_thms ()

step_total () 
get_all_const_specifications ()
!the_enum_brackets 
get_all_enum_info ()
get_all_fixities()
get_all_fun_definitions ()
get_language_level_mode ()
!the_relative_step_start 
!the_tyconst_defs 
!the_type_annotation_mode 
!the_type_bijections 
!the_type_fixities 
!the_tyvar_marking_mode 
!the_var_marking_mode 

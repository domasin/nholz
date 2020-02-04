#I "../bin/netstandard2.0"
#r "nholz.dll"

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

#I "../bin/netstandard2.0"
#r "nholz.dll"
open HOL
fsi.AddPrinter print_type
fsi.AddPrinter print_qtype
fsi.AddPrinter print_term
fsi.AddPrinter print_qterm
fsi.AddPrinter print_thm
//fsi.AddPrinter print_graph

//CoreThry.load
//Equal.load
//Bool.load

//let x = parse_term(@"x:'a") 
//let f = parse_term(@"f:'a->'b")
//let g = parse_term(@"g:'a->'b")

//let th1 = @"\x. (f:'a->'b) x" |> parse_term |> eta_conv_tr
//let th2 = sym_rule_tr th1
//let th3 = @"!x. (f:'a->'b) x = g x" |> parse_term |> assume_rule_tr
//let th4 = spec_rule_tr x th3
//let th5 = mk_abs_rule_tr x th4
//let th6 = @"\x. (g:'a->'b) x" |> parse_term |> eta_conv_tr
//let th7 = [th2; th5; th6] |> list_trans_rule_tr
//let th8 = @"(f:'a->'b)=g" |> parse_term |> assume_rule_tr
//let th9 = mk_comb1_rule_tr th8 x
//let th10 = gen_rule_tr x th9
//let th11 = deduct_antisym_rule_tr th7 th10
//let th = list_gen_rule_tr [f;g] th11

//th |> snd |> view




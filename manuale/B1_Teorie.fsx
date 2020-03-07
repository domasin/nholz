(**

TEORIE
=============

TOERIA CORE
------------

**Costani di Tipo**
*)
// bool             `:bool`                         Nonfix
// ->               `:'1->'2`                       Infix (5, RightAssoc)
(**

**Costanti**
*)
   
// true             `:bool`                         Nonfix
// ==>              `:bool->bool->bool`             Infix (10, RightAssoc)
// /\               `:bool->bool->bool`             Infix (20, RightAssoc)
// =                `:'a->'a->bool`                 Infix (30, NonAssoc)
// @                `:('a->bool)->'a`               Binder
// !                `:('a->bool)->bool`             Binder
// ?                `:('a->bool)->bool`             Binder
// ONE_ONE          `:('a->'b)->bool`               Nonfix
// TYPE_DEFINITION  `:('a->bool)->('b->'a)->bool`   Nonfix

(**
**Costanti Alias**

L'unico alias supportato &egrave; `<=>`, per un'istanza di tipo di `=`.

*)

// <=>              `:bool->bool->bool`             Infix (5, NonAssoc)

(**
**Definizioni**
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
(***unhide***)

true_def                                                  // istanza della proprieta' riflessiva di uguaglianza per la 
// |- true <=> (\(p:bool). p) = (\p. p)                   // funzione d'identita' booleana

conj_def                                                  // funzione binaria che restituisce se il fatto che i due 
// |- $/\ = (\p1 p2. !p. (p1 ==> (p2 ==> p)) ==> p)       // argomenti inisieme implichino il valore, implica il valore

forall_def                                                // funzione che restituisce se il predicato restituisce true per 
// |- $! = (\(P:'a->bool). P = (\x. true))                // ogni input

exists_def                                                // funzione che restituisce per un P se un qualsiasi elemento 
// |- $? = (\(P:'a->bool). P ($@ P))                      // selezionato come soddisfacente il predicato necessariamente  
                                                          // soddisfa il predicato

one_one_def                                               // funzione che restituisce se la funzione argomento e'  
// |- ONE_ONE =                                           // iniettiva, cioe' se l'uguaglianza dei valori per due argomenti   
//     (\(f:'a->'b). !x1 x2. f x1 = f x2 ==> x1 = x2)     // implica ncessariamente l'uguaglianza dei due argomenti

type_definition_def                                       // funzione che prende un predicato per elementi del tipo di 
// |- TYPE_DEFINITION =                                   // rappresentazione e un mapping da elementi del nuovo tipo al 
//     (\P (rep:'b->'a). ONE_ONE rep                      // tipo di  rappresentazione e restituisce se il mapping e' 
//                     /\ (!x. P x <=> (?y. x = rep y)))  // iniettivo e mappa su  elementi che  soddisfano il predicato. 
                                                          // E' usata per definire nuove costanti di tipo

(**
**Assiomi**
*)

eta_ax                                                     // per ogni funzione f la lambda astrazione dell'applicazione
// |- !(f:'a->'b). (\x. f x) = f                           // di f a alla variabile lambda e' uguale alla funzione stessa
   
imp_antisym_ax                                             // proprieta' antisimmetrica dell'implicazione
// |- !p1 p2. (p1 ==> p2) ==>                               
//              ((p2 ==> p1) ==> (p1 <=> p2))               
   
select_ax                                                  // per ogni P e x, se x soddisfa P, allora P e' soddisfatto  
// |- !(P:'a->bool) x. P x ==> P ($@ P)                    // anche dall'elemento selezionato per P

(**
Logica Predicativa
------------------

**Costanti**
*)

// false            `:bool`                         Nonfix
// ~                `:bool->bool`                   Prefix
// \/               `:bool->bool->bool`             Infix (15, RightAssoc)
// ?!               `:('a->bool)->bool`             Binder
// LET              `:('a->'b)->'a->'b`             Nonfix *
// ONTO             `:('a->'b)->bool`               Nonfix
// COND             `:bool->'a->'a->'a`             Nonfix *

(*** hide ***)

//(**
//DEFINITIONS

//false_def
//   |- false <=> (!p. p)

//not_def
//   |- $~ = (\p. p ==> false)

//disj_def
//   |- $\/ = (\p1 p2. !p. (p1 ==> p) ==> (p2 ==> p) ==> p)

//uexists_def
//   |- $?! = (\(P:'a->bool). ?x. P x /\ (!y. P y ==> y = x))

//let_def
//   |- LET = (\(f:'a->'b) x. f x)

//onto_def
//   |- ONTO = (\(f:'a->'b). !y. ?x. y = f x)

//cond_def
//   |- COND =
//        (\p (t1:'a) t2.
//            @x. ((p <=> true) ==> x = t1) /\ ((p <=> false) ==> x = t2))

//********************************************************************************

//                                  PAIRS

//TYPE CONSTANTS

//#                `:'1#'2`                        Infix (10, RightAssoc)

//CONSTANTS

//MkPairRep        `:'a->'b->'a->'b->bool`         Nonfix
//IsPairRep        `:('a->'b->bool)->bool`         Nonfix
//PairAbs          `:('a->'b->bool)->'a#'b`        Nonfix
//PairRep          `:'a#'b->'a->'b->bool`          Nonfix
//PAIR             `:'a->'b->'a#'b`                Nonfix *
//FST              `:'a#'b->'a`                    Nonfix
//SND              `:'a#'b->'b`                    Nonfix

//TYPE DEFINITIONS

//prod_def
//   |- ?(f:'a#'b->'a->'b->bool). TYPE_DEFINITION IsPairRep f

//DEFINITIONS

//mk_pair_rep_def
//   |- MkPairRep = (\(x:'a) (y:'b) a b. a = x /\ b = y)

//is_pair_rep_def
//   |- IsPairRep = (\(r:'a->'b->bool). ?a b. r = MkPairRep a b)

//prod_def
//   |- ?(f:'a#'b->'a->'b->bool). TYPE_DEFINITION IsPairRep f

//prod_bij_def1
//   |- !(a:'a#'b). PairAbs (PairRep a) = a

//prod_bij_def2
//   |- !(r:'a->'b->bool). IsPairRep r <=> PairRep (PairAbs r) = r

//pair_def
//   |- PAIR = (\(x:'a) (y:'b). PairAbs (MkPairRep x y))

//fst_def
//   |- FST = (\(p:'a#'b). @x. ?y. p = (x,y))

//snd_def
//   |- SND = (\(p:'a#'b). @y. ?x. p = (x,y))


//********************************************************************************

//                                INDIVIDUALS

//TYPE CONSTANTS

//ind              `:ind`                          Nonfix

//CONSTANTS

//IND_ZERO         `:ind`                          Nonfix
//IND_SUC          `:ind->ind`                     Nonfix

//DEFINITIONS

//ind_suc_zero_spec
//   |- ONE_ONE IND_SUC /\ (!i. ~ (IND_SUC i = IND_ZERO))

//AXIOMS

//infinity_ax
//   |- ?(f:ind->ind). ONE_ONE f /\ ~ ONTO f

//********************************************************************************

//                              NATURAL NUMBERS

//TYPE CONSTANTS

//nat              `:nat`                          Nonfix

//CONSTANTS

//IsNatRep         `:ind->bool`                    Nonfix
//NatAbs           `:ind->nat`                     Nonfix
//NatRep           `:nat->ind`                     Nonfix
//ZERO             `:nat`                          Nonfix
//SUC              `:nat->nat`                     Nonfix
//PRE              `:nat->nat`                     Nonfix
//+                `:nat->nat->nat`                Infix (50, LeftAssoc)
//-                `:nat->nat->nat`                Infix (50, LeftAssoc)
//*                `:nat->nat->nat`                Infix (55, LeftAssoc)
//EXP              `:nat->nat->nat`                Infix (60, LeftAssoc)
//EVEN             `:nat->bool`                    Nonfix
//ODD              `:nat->bool`                    Nonfix
//<                `:nat->nat->bool`               Infix (40, NonAssoc)
//<=               `:nat->nat->bool`               Infix (40, NonAssoc)
//>                `:nat->nat->bool`               Infix (40, NonAssoc)
//>=               `:nat->nat->bool`               Infix (40, NonAssoc)
//BIT0             `:nat->nat`                     Nonfix
//BIT1             `:nat->nat`                     Nonfix
//NUMERAL          `:nat->nat`                     Nonfix

//TYPE DEFINITIONS

//nat_def
//   |- ?(f:nat->ind). TYPE_DEFINITION IsNatRep f

//DEFINITIONS

//is_nat_rep_def
//   |- !i. IsNatRep i <=> (!P. P IND_ZERO /\ (!j. P j ==> P (IND_SUC j)) ==> P i)

//nat_bij_def1
//   |- !a. NatAbs (NatRep a) = a

//nat_bij_def2
//   |- !r. IsNatRep r <=> NatRep (NatAbs r) = r

//zero_def
//   |- ZERO = NatAbs IND_ZERO

//suc_def
//   |- !n. SUC n = NatAbs (IND_SUC (NatRep n))

//pre_def
//   |- PRE 0 = 0 /\ (!n. PRE (SUC n) = n)

//add_def
//   |- (!n. 0 + n = n) /\ (!m n. SUC m + n = SUC (m + n))

//sub_def
//   |- (!n. n - 0 = n) /\ (!m n. m - SUC n = PRE (m - n))

//mult_def
//   |- (!n. 0 * n = 0) /\ (!m n. SUC m * n = n + m * n)

//exp_def
//   |- (!n. n EXP 0 = 1) /\ (!m n. m EXP SUC n = m * m EXP n)

//even_def
//   |- (EVEN 0 <=> true) /\ (!n. EVEN (SUC n) <=> ~ EVEN n)

//odd_def
//   |- !n. ODD n <=> ~ EVEN n

//lt_def
//   |- (!m. m < 0 <=> false) /\ (!m n. m < SUC n <=> m = n \/ m < n)

//le_def
//   |- !m n. m <= n <=> m < n \/ m = n

//gt_def
//   |- !m n. m > n <=> n < m

//ge_def
//   |- !m n. m >= n <=> n <= m

//bit0_def
//   |- (BIT0 ZERO = ZERO) /\ (!n. BIT0 (SUC n) = SUC (SUC (BIT0 n)))

//bit1_def
//   |- !n. BIT1 n = SUC (BIT0 n)

//numeral_def
//   |- !n. NUMERAL n = n

//*)
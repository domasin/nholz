(**

TEORIE
=============

Teoria Core
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



(**
**Definizioni**
*)

false_def                                                    // falsita'
// |- false <=> (!p. p)                                      //

not_def                                                      // negazione logica
// |- $~ = (\p. p ==> false)                                 // 

disj_def                                                     // digiunzione
// |- $\/ = (\p1 p2. !p. (p1 ==> p) ==> (p2 ==> p) ==> p)    // 

uexists_def                                                  // quantificazione esistenziale univoca
// |- $?! = (\(P:'a->bool). ?x. P x /\ (!y. P y ==> y = x))  // 

let_def                                                      // espressioni let: `LET (LET (\x1 x2. t) s1) s2`
// |- LET = (\(f:'a->'b) x. f x)                             // e' stampato come `let x1 = s1 and x2 = s2 in t`  

onto_def                                                     // suriettivita'
// |- ONTO = (\(f:'a->'b). !y. ?x. y = f x)                  // 

cond_def                                                     // espressioni condizionali
// |- COND =                                                 // `COND c t1 t2` e stampato come
//     (\p (t1:'a) t2.                                       // `if c then t1 else t2`
//         @x. ((p <=> true) ==> x = t1)                     // 
//              /\ ((p <=> false) ==> x = t2))               // 


(**
Coppie ordinate
--------------

**Costanti di tipo**
*)

// #                `:'1#'2`                        Infix (10, RightAssoc)

(**
**Costanti**
*)

// MkPairRep        `:'a->'b->'a->'b->bool`         Nonfix
// IsPairRep        `:('a->'b->bool)->bool`         Nonfix
// PairAbs          `:('a->'b->bool)->'a#'b`        Nonfix
// PairRep          `:'a#'b->'a->'b->bool`          Nonfix
// PAIR             `:'a->'b->'a#'b`                Nonfix *
// FST              `:'a#'b->'a`                    Nonfix
// SND              `:'a#'b->'b`                    Nonfix

(**
**Definizioni di tipo**
*)

prod_def
// |- ?(f:'a#'b->'a->'b->bool). TYPE_DEFINITION IsPairRep f

(**
**Definizioni**
*)

mk_pair_rep_def                                         // la funzione di rappresentazione restituisce vero solo 
// |- MkPairRep =                                       // quando ogni argomento e' uguale al suo corrispondente
//     (\(x:'a) (y:'b) a b. a = x /\ b = y)             // elemento nella coppia

is_pair_rep_def                                         // la funzione caratteristica per l'operatore di tipo prodotto.
// |- IsPairRep =                                       // Prende la funzione di rappresentazione e restituisce vero se 
//     (\(r:'a->'b->bool). ?a b. r = MkPairRep a b)     // esiste una coppia per cui ne e' la concreta rappresentazione

prod_def                                                // definizione del tipo prodotto
// |- ?(f:'a#'b->'a->'b->bool).                         // 
//                   TYPE_DEFINITION IsPairRep f        // 

prod_bij_def1                                           // biiezioni del tipo prodotto
// |- !(a:'a#'b). PairAbs (PairRep a) = a               // 
                                                        // 
prod_bij_def2                                           // 
// |- !(r:'a->'b->bool).                                // 
//       IsPairRep r <=> PairRep (PairAbs r) = r        // 

pair_def                                                // funzione di accoppiamento. E' definita come l'astrazione del 
// |- PAIR =                                            // tipo prodotto della funzione 
//     (\(x:'a) (y:'b). PairAbs (MkPairRep x y))        // PAIR t1 t2 e' elaborata e stampata come (t1,t2).

fst_def                                                 // seleziona il primo componente della coppia
// |- FST = (\(p:'a#'b). @x. ?y. p = (x,y))             //

snd_def                                                 // seleziona il secondo componente della coppia
// |- SND = (\(p:'a#'b). @y. ?x. p = (x,y))             // 


(**
Individui
--------------

**Costanti di tipo**
*)
// ind              `:ind`                          Nonfix

(**
**Costanti**
*)

// IND_ZERO         `:ind`                          Nonfix
// IND_SUC          `:ind->ind`                     Nonfix

(**
**Definizioni**
*)
ind_suc_zero_spec
// |- ONE_ONE IND_SUC /\ (!i. ~ (IND_SUC i = IND_ZERO))

(**
**Assiomi**
*)

infinity_ax                                             // l'assioma dell'infinito dichiara che il nuovo tipo degli
// |- ?(f:ind->ind). ONE_ONE f /\ ~ ONTO f              // individui e' infinito affermando che esiste una funzione
                                                        // totale iniettiva da individui a individui che non e'
                                                        // suriettiva

(**
Numeri naturali
---------------

**Costanti di tipo**
*)

// nat              `:nat`                          Nonfix

(**
**Costanti**
*)

// IsNatRep         `:ind->bool`                    Nonfix
// NatAbs           `:ind->nat`                     Nonfix
// NatRep           `:nat->ind`                     Nonfix
// ZERO             `:nat`                          Nonfix
// SUC              `:nat->nat`                     Nonfix
// PRE              `:nat->nat`                     Nonfix
// +                `:nat->nat->nat`                Infix (50, LeftAssoc)
// -                `:nat->nat->nat`                Infix (50, LeftAssoc)
// *                `:nat->nat->nat`                Infix (55, LeftAssoc)
// EXP              `:nat->nat->nat`                Infix (60, LeftAssoc)
// EVEN             `:nat->bool`                    Nonfix
// ODD              `:nat->bool`                    Nonfix
// <                `:nat->nat->bool`               Infix (40, NonAssoc)
// <=               `:nat->nat->bool`               Infix (40, NonAssoc)
// >                `:nat->nat->bool`               Infix (40, NonAssoc)
// >=               `:nat->nat->bool`               Infix (40, NonAssoc)
// BIT0             `:nat->nat`                     Nonfix
// BIT1             `:nat->nat`                     Nonfix
// NUMERAL          `:nat->nat`                     Nonfix

(**
**Definizioni di tipo**
*)

nat_def
// |- ?(f:nat->ind). TYPE_DEFINITION IsNatRep f

(**
**Definizioni**
*)

is_nat_rep_def                                   // funzione caratteristica dei naturali definita come quella funzione che 
// |- !i. IsNatRep i <=>                         // restituisce vero per un elemento di ind sse qualsiasi proprieta' che 
//    (!P. P IND_ZERO /\                         // valga per IND_ZERO e tutti i suoi successori sotto IND_SUCC vale 
//       (!j. P j ==> P (IND_SUC j)) ==> P i)    // necessariamente anche per l'elemento. Questo da il piu' piccolo sotto-
                                                 // insieme di ind che contiene IND_ZERO ed e' chiuso sotto IND_SUC

nat_bij_def1                                     // biiezioni del tipo dei naturali
// |- !a. NatAbs (NatRep a) = a                  //
                                                 //
nat_bij_def2                                     //
// |- !r. IsNatRep r <=> NatRep (NatAbs r) = r   //

zero_def                                         // ZERO e SUCC sono definiti in termini dei loro equivalenti nel tipo 
// |- ZERO = NatAbs IND_ZERO                     // degli individui
                                                 //
suc_def                                          //
// |- !n. SUC n = NatAbs (IND_SUC (NatRep n))    //

pre_def
// |- PRE 0 = 0 /\ (!n. PRE (SUC n) = n)

add_def
// |- (!n. 0 + n = n) 
//         /\ (!m n. SUC m + n = SUC (m + n))

sub_def
// |- (!n. n - 0 = n) 
//         /\ (!m n. m - SUC n = PRE (m - n))

mult_def
// |- (!n. 0 * n = 0) 
//         /\ (!m n. SUC m * n = n + m * n)

exp_def
// |- (!n. n EXP 0 = 1) 
//         /\ (!m n. m EXP SUC n = m * m EXP n)

even_def
// |- (EVEN 0 <=> true) 
//         /\ (!n. EVEN (SUC n) <=> ~ EVEN n)

odd_def
// |- !n. ODD n <=> ~ EVEN n

lt_def
// |- (!m. m < 0 <=> false) 
//        /\ (!m n. m < SUC n <=> m = n \/ m < n)

le_def
// |- !m n. m <= n <=> m < n \/ m = n

gt_def
// |- !m n. m > n <=> n < m

ge_def
// |- !m n. m >= n <=> n <= m

(**

I numeri naturali sono definiti in termini di `SUC` e dell'addizione. La rappresentazione implica l'applicare una sequenza di operatori
`BIT0` e `BIT1` alla costante `ZERO`, con `NUMERAL` come un tag che viene applicato al risultato. Sia `BIT0` che `BIT1` duplicano il loro 
argmento aggiungendo rispettivamente 0 o 1. Il tag `NUMERAL` semplicemente ritorna il suo argomento, ed &egrave; usato per identicare 
atomi di numerali nei termini. Letta dall'interno all'esterno, una sequenza di `BIT0` e `BIT1` corrisponde direttamente agli 0 e agli 1 
della notazione binaria. 

Ad esempio, il numero 6 &egrave; rappresentato da `NUMERAL (BIT0 (BIT1 (BIT1 ZERO)))` o 110 in binario.
*)

bit0_def                                           
// |- (BIT0 ZERO = ZERO)                           
//     /\ (!n. BIT0 (SUC n) = SUC (SUC (BIT0 n)))  
                                                   
bit1_def                                           
// |- !n. BIT1 n = SUC (BIT0 n)                    
                                                   
numeral_def                                        
// |- !n. NUMERAL n = n                            
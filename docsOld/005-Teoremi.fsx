(**
TEOREMI
=============

Per i teoremi gi&agrave; documentati, cliccando sul nome del teorema si apre una pagina 
di dettaglio con l'esposizione della dimostrazione a codice e un rendering della dimostrazione nel calcolo 
dei sequenti. 

Laddove sono disponibili, per le regole di inferenza utilizzate, vengono usate delle estensioni 
al sistema base con dimostrazioni ad albero, strategie di dimostrazioni all'indietro e un opzione `view`
di visualizzazione dell'albero di dimostrazione in LaTeX.

Queste estensioni non sono derivate da Hol Zero e sono in corso di implementazione. 

**[truth\_thm](teoremi\0001_truth.html)**

$\vdash \top$

vero &egrave; derivabile

**[fun\_eq\_thm](0002_fun_eq.html)**

$\vdash \forall (f:\alpha \rightarrow \beta)\ g.\ f = g\ \Leftrightarrow\ (\forall x.\ f\ x = g\ x)$

L'euivalenza tra funzioni corrisponde all'equivalenza dei loro valori a parit&agrave; di argomento


Propriet&agrave; algebriche degli operatori logici
------------

**[not\_true\_thm](0003_not_true.html)**

$\vdash \neg \top \Leftrightarrow \bot$

non vero equivale a falso

**[not\_false\_thm](0004_not_false.html)**

$\vdash \neg \bot \Leftrightarrow \top$

non falso equivale a vero

**[true\_not\_eq\_false\_thm](0005_true_not_eq_false.html)**

$\vdash \neg (\top \Leftrightarrow \bot)$

vero non equivale a falso

**[not\_dist\_disj\_thm](0006_not_dist_disj.html)**

$\forall p\ q.\ \neg (p \vee q) \Leftrightarrow \neg p \wedge \neg q$

ditribuzione della negazione sulla disgiunzione

**[conj\_id\_thm](0007_conj_id.html)**

$\forall p.\ p \wedge \top \Leftrightarrow p$

vero &egrave; l'identit&agrave; della congiunzione

**[conj\_zero\_thm](0008_conj_zero.html)**

$\forall p.\ p \wedge \bot \Leftrightarrow \bot$

congiunzione zero

**[conj\_idem\_thm](0009_conj_idem.html)**

$\forall p.\ p \wedge p \Leftrightarrow p$

congiunzione idem

**[conj\_comm\_thm](0010_conj_comm.html)**

$\forall p.\ p \wedge q \Leftrightarrow q \wedge p$

commutativit&agrave; della congiunzione

**[conj\_assoc\_thm](0011_conj_assoc.html)**

$\forall p\ q\ r.\ p \wedge (q \wedge r) \Leftrightarrow (p \wedge q) \wedge r$

associativit&agrave; della congiunzione

**[conj\_absorb\_disj\_thm](0012_conj_absorb_disj.html)**

$\forall p\ q.\ p \wedge (p \vee q) \Leftrightarrow p$

assorbimento della disgiunzione nella congiunzione

**[conj\_dist\_right\_disj\_thm](0013_conj_dist_right_disj.html)**

$\forall p\ q\ r.\ p \wedge (q \vee r) \Leftrightarrow (p \wedge q) \vee (p \wedge r)$

distributivit&agrave; a destra della congiunzione sulla disgiunzione

**[conj\_dist\_left\_disj\_thm](0014_conj_dist_left_disj.html)**

$\forall p\ q\ r.\ (p \vee q) \wedge r \Leftrightarrow (p \wedge r) \vee (q \wedge r)$

distributivit&agrave; a sinistra della congiunzione sulla disgiunzione

work in prog...

**[disj\_id\_thm](0016_disj_id.html)**

$\vdash \forall p.\ p \vee \bot \Leftrightarrow p$

falso &egrave; l'identit&agrave; della disgiunzione

**[disj\_zero\_thm](0017_disj_zero.html)**

$\vdash \forall p.\ p \vee \top \Leftrightarrow \top$

**[disj\_idem\_thm](0018_disj_idem.html)**

$\vdash \forall p.\ p \vee p \Leftrightarrow p$



...

Logica classica
----------------

Tutti i teoremi seguenti sono derivati attraverso l'assioma di scelta e pertanto 
possono essere considerati come logica classica.

Va comunque notato che alcuni sono di fatto derivabili nella logica intuizionista 
se si utilizza una definizione alternativa dell quantificatore esistenziale 
(come in HOL Light).

**[excluded\_middle\_thm](0044_excluded_midle.html)**

$\vdash \forall p.\ p \vee \neg p$

Per ogni proposizione, o essa &egrave; dimostrabile o lo &egrave; la sua negazione

**[bool\_cases\_thm](0045_bool_cases.html)**

$\vdash \forall p.\ (p \Leftrightarrow \top) \vee (p \Leftrightarrow \bot)$

Per ogni proposizione, o essa equivale a true oppure equivale a false

...

*)

(**
Work in progress
-----
*)

(***hide***)
#load "avvio.fsx"
open HOL
(***unhide***)

cond_false_thm
// |- !(t1:'a) t2. (if false then t1 else t2) = t2

cond_idem_thm
// |- !p (t:'a). (if p then t else t) = t

cond_not_thm
// |- !p (t1:'a) t2. (if (~ p) then t1 else t2) = (if p then t2 else t1)

cond_true_thm
// |- !(t1:'a) t2. (if true then t1 else t2) = t1


conj_contr_thm
//   |- !p. p /\ ~ p <=> false


disj_absorb_conj_thm
//   |- !p q. p \/ (p /\ q) <=> p

disj_assoc_thm
//   |- !p q r. p \/ (q \/ r) <=> (p \/ q) \/ r

disj_comm_thm
//   |- !p q. p \/ q <=> q \/ p

disj_dist_left_conj_thm
//   |- !p q r. (p /\ q) \/ r <=> (p \/ r) /\ (q \/ r)

disj_dist_right_conj_thm
//   |- !p q r. p \/ (q /\ r) <=> (p \/ q) /\ (p \/ r)

exists_dist_disj_thm
//   |- !(P:'a->bool) Q. (?x. P x \/ Q x) <=> (?x. P x) \/ (?x. Q x)

exists_null_thm
//   |- !t. (?(x:'a). t) <=> t

exists_one_point_thm
//   |- !(P:'a->bool) a. (?x. x = a /\ P x) <=> P a

//exists_value_thm
//   |- !(x:'a). ?y. y = x

forall_dist_conj_thm
//   |- !(P:'a->bool) Q. (!x. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)

forall_null_thm
//   |- !t. (!(x:'a). t) <=> t

forall_one_point_thm
//   |- !(P:'a->bool) a. (!x. x = a ==> P x) <=> P a

//imp_alt_def_thm
//   |- $==> = (\p q. p /\ q <=> p)

imp_disj_thm
//   |- !p q. (p ==> q) <=> (~ p \/ q)

imp_dist_left_disj_thm
//   |- !p q r. (p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)

imp_dist_right_conj_thm
//   |- !p q r. (p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)

//imp_imp_thm
//   |- !p q r. (p ==> q ==> r) <=> (p /\ q ==> r)

imp_left_id_thm
//   |- !p. (true ==> p) <=> p

imp_left_zero_thm
//   |- !p. false ==> p

imp_refl_thm
//   |- !p. p ==> p

imp_right_zero_thm
//   |- !p. p ==> true

not_dist_conj_thm
//   |- !p q. ~ (p /\ q) <=> ~ p \/ ~ q



not_dist_exists_thm
//   |- !(P:'a->bool). ~ (?x. P x) <=> (!x. ~ P x)

not_dist_forall_thm
//   |- !(P:'a->bool). ~ (!x. P x) <=> (?x. ~ P x)

not_dneg_thm
//   |- !p. ~ ~ p <=> p

select_eq_thm
//   |- !(a:'a). (@x. x = a) = a

skolem_thm
//   |- !(P:'a->'b->bool). (!x. ?y. P x y) <=> (?f. !x. P x (f x))

uexists_thm1
//   |- !(P:'a->bool). (?!x. P x) <=> (?x. P x /\ (!y. P y ==> y = x))

uexists_thm2
//   |- !(P:'a->bool). (?!x. P x) <=> (?x. !y. P y <=> x = y)

uexists_thm3
//   |- !(P:'a->bool). (?!x. P x)
//                     <=> (?x. P x) /\ (!x' x''. P x' /\ P x'' ==> x' = x'')

uexists_one_point_thm
//   |- !(P:'a->bool) a. (?!x. x = a /\ P x) <=> P a

unique_skolem_thm
//   |- !(P:'a->'b->bool). (!x. ?!y. P x y) <=> (?f. !x y. P x y <=> f x = y)




(**
PAIRS
----
*)

fst_snd_thm
//   |- !(p:'a#'b). (FST p, SND p) = p

fst_thm
//   |- !(x:'a) (y:'b). FST (x,y) = x

pair_eq_thm
//   |- !(x:'a) (y:'b) u v. (x,y) = (u,v) <=> x = u /\ y = v

pair_surjective_thm
//   |- !(p:'a#'b). ?x y. p = (x,y)

snd_thm
//   |- !(x:'a) (y:'b). SND (x,y) = y

(**
INDIVIDUALS
----
*)

ind_suc_injective_thm
//   |- !i j. IND_SUC i = IND_SUC j <=> i = j

ind_suc_not_zero_thm
//   |- !i. ~ (IND_SUC i = IND_ZERO)

(**
NATURAL NUMBERS
----
*)

add_assoc_thm
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
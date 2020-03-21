(**
Regole d'inferenza
==================

Questa appendice fornisce una descrizione delle regole d'inferenza
*)

(**

| Bool.add\_asm\_rule 
--------------

Questa &egrave; la regola di aggiunta di un'assunzione. Prende un termine booleano 
e un teorema e restituisce lo stesso teorema ma con il termine fornito aggiunto 
alle sue assunzioni. Il teorema restituito in output coincide con quello fornito in input 
se il termine &egrave; gi&agrave; presente nelle assunzioni.

*)

(*** hide ***)
#I "../bin/netstandard2.0"
#r "nholz.dll"
open HOL
(*** unhide ***)

add_asm_rule

//  `q`   A |- p
//  ------------
//  A u {q} |- p

(**

| Equal.alpha\_conv
--------------

Questa &egrave; la regola di alfa conversione. Sostituisce la variabile legata 
e tutte le sue occorrenze nel termine di lambda astrazione  fornito (il secondo 
argomento) con la variabile fornita (come primo argomento).

Si veda anche alpha\_link\_conv.
*)

alpha_conv

//        `y`   `\x. t`
//  -------------------------
//  |- (\x. t) = (\y. t[y/x])


(**

| Equal.alpha\_link\_conv
--------------

Questa &egrave; la regola di conversione alfa linking. Prende due termini 
alfa-equivalentei e restituisce un terorema che afferma che il secondo &egrave; 
uguale al primo, senza alcuna assunzione. Fallisce se i termini forniti non sono 
alfa equivalenti.

*)

alpha_link_conv

//   `t'`   `t`                                                              
//   ----------                                                              
//   |- t = t'      

(**

| Equal.app\_beta\_rhs\_rule
--------------

Questa regola &egrave; utilizzata per espandere una funzione definita in termini 
di una lambda astrazione. Prende un teorema di uguaglianza e un termine, dove 
la parte destra del teorema &egrave; una lambda astrazione con una variabile 
legata dello stesso tipo del termine argomento. Restituisce un teorema che 
afferma che l'argomento sinistro del teorema applicato al termine in input 
&egrave; uguale alla beta riduzione della lambda astrazione applicata al termine 
in input.

*)

app_beta_rhs_rule

//    A |- f = (\v. t)   `s`                                                  
//   -----------------------                                                  
//     A |- f s = t[s/v]     

(**

| Wrap.assume\_rule                                          
-------------------

Regola primitiva.

Questa &egrave; la regola di assunzione. Prende un termine booleano, e restituisce 
un teorema che afferma che il termine vale sotto la singola assunzione del termine 
stesso.

Si veda anche: add\_asm\_rule.

*)

assume_rule

//     `p`
//   --------
//   {p} |- p

(**

| Wrap.beta\_conv                                         
-------------------

Regola primitiva.

Questa &egrave; la conversione di beta riduzione. Prende una lambda astrazione 
applicata a un termine, e restituisce un teorema che afferma che l'applicazione 
&egrave; uguale al corpo della lambda astrazione con tutte le occorrenze della 
variabile legata sostituita con l'argomento dell'apllicazione, senza alcuna 
assunzione.

*)

beta_conv

//         `(\x. t) s`
//    ---------------------
//    |- (\x. t) s = t[s/x]

(**

| Bool.bspec\_rule                                        
-------------------

Questa &egrave; la regola di eliminazione del quantifcatore universale con 
beta-riduzione. Toglie il quantificatore universale pi&ugrave; esterno dal 
teorema fornito, e sostituisce nel corpo ogni occorrenza della variabile legata 
eliminata con il termine fornito. Se il termine in input &egrave; una lambda 
astrazione, esegue anche la beta riduzione di ogni occorrenza sostituita che 
sia applicata ad un argomento. Il tipo del termine fornito deve essere uguale 
al tipo della variabile legata eliminata.

Si veda anche: spec\_rule, list\_spec\_rule, spec\_all\_rule, gen\_rule.

*)

bspec_rule

//         `\y. t`   A |- !x. p
//   --------------------------------
//   A |- p[ \y.t / x; t[s/y] / x s ]

(**

| BoolClass.ccontr\_rule                                        
-------------------

Questa &egrave; la regola contraddizione della logica classica. Prende un termine 
booleano e un teorema con falso come sua conclusione. Restituisce un teorema con 
il termine fornito come sua conclusione, e con le stesse assunzioni del teorema 
fornito ma con la negazione logica del termine fornito rimossa. Si noti che la 
negazione logica del termine fornito non deve essere nelle assunzioni del teorema 
affinch&eacute; questa regola abbia successo.

Si veda anche: contr\_rule, deduct\_contrapos\_rule.

*)

ccontr_rule

//  `p`   A |- false
//  ----------------
//    A\{~p} |- p

(**

| Bool.choose\_rule                                        
-------------------

Questa &egrave; la regola di eliminazione del quantificatore esistenziale.
Rimuove, dalle assunzioni di un teorema principale fornito, il corpo di un 
teorema esistenziale fornito (ma con tutte le occorrenze della variabile 
legata sostituite con una variabile fornita), e aggiunge le assunzioni del 
teorema esistenziale. Alla variabile fornita non &egrave; permesso di essere 
libera nella conclusione del teorema esistenziale o nelle altre assuzioni del 
teorema principale originario o nella sua conclusione. Si noti che il corpo 
alterato del teorema esistenziale non deve essere presente nelle assunzioni 
del teorema principale affinch&eacute; questa regola abbia successo.

See also: exists\_rule, mk_exists\_rule.

*)

choose_rule

//    `y`   A1 |- ?x. p    A2 |- q      [ con "y" non libera in:                    
//    -----------------------------         `?x. p`, `q` o `A2\{p[y/x]}` ]   
//        A1 u A2\{p[y/x]} |- q               

(**

| Bool.conj\_rule                                       
-------------------

Questa &egrave; la regola di e-introduzione. Congiunge i due teoremi forniti
e unisce le loro assunzioni.

Si veda anche: conjunct1\_rule, conjunct2\_rule, mk\_conj\_rule.

*)

conj_rule

//   A1 |- p    A2 |- q                                                   
//   ------------------                                                   
//   A1 u A2 |- p /\ q 

(**

| Bool.conjunct1\_rule                                      
-------------------

Questa &egrave; la regola di e-eliminazione a sinistra. Rimuove il 
congiunto a destra dal teorema di congiuzione fornito.

Si veda anche: conjunct2\_rule, conjunct\_rule, mk\_conj\_rule.

*)

conjunct1_rule

//   A |- p /\ q                                                             
//   -----------                                                             
//     A |- p   

(**

| Bool.conjunct2\_rule                                      
-------------------

Questa &egrave; la regola di e-eliminazione a destra. Rimuove il 
congiunto a sinistra dal teorema di congiuzione fornito.

Si veda anche: conjunct1\_rule, conjunct\_rule, mk\_conj\_rule.

*)

conjunct2_rule

//   A |- p /\ q                                                             
//   -----------                                                             
//     A |- q   

(**

| Bool.contr\_rule                                      
-------------------

Questa &egrave; la regola di contraddizione della logica intuizionista. Prende 
un termine booleano e un teorema con falso come conclusione. Restituisce un 
teorema con il termine fornito come sua conclusione, sotto le stess assunzioni 
del teorema fornito.

See also: ccontr\_rule, deduct\_contrapos\_rule.

*)

contr_rule

//  `p`   A |- false                                                       
//  ----------------                                                       
//       A |- p        

(**

| Bool.deduct\_antisym\_rule                                      
-------------------

Questa &egrave; la regola di antisimmetria per la deduzione. Prende due 
teoremi come argomenti. Restituisce un teorema che afferma che le conclusioni 
fornite sono equivalente, sotto l'unione delle assunzioni ma con la conclusione 
di un teorema rimossa dalle assunzioni dell'altro

See also: imp\_antisym\_rule, undisch\_rule.

*)

deduct_antisym_rule

//       A1 |- p    A2 |- q      
//   --------------------------              
//   A1\{q} u A2\{p} |- p <=> q   

(**

| Bool.deduct\_contrapos\_rule                                      
-------------------

Questa &egrave; la regola di contraddizione per la deduzione. Scambia e 
nega logicamente il termine dell'assunzione fornita e la conclusione del 
teorema fornito. Si noti che il termine fornito non deve essere presente 
nelle assunzioni del teorema di input perhc&eacute; la regola abbia successo. 
Se la negazione logica della conclusione del teorema in input coincide con 
il termine fornito, allora non occorrer&agrave; nelle assunzioni del teorema 
risultante.

See also: not\_intro\_rule, disch\_rule, contr\_rule, ccontr\_rule.

*)

deduct_contrapos_rule

//       `q`   A |- p                                                     
//   ---------------------                                                
//   (A u {~p})\{q} |- ~ q      

(**

| Wrap.disch\_rule                                     
-------------------

Regola primitiva

Questa &egrave; la regola d'intrdouzone dell'implicazione. Prende un termine booleano 
e un teorema, rimuove il termine (se presente) dalle assunzioni del teorema e lo 
aggiunge come antecedente della conclusione. Si noti che il termine non deve essere 
presente nelle assunzioni del teorema fornito perch&eacute; la regola abbia 
successo.

Si veda anche: undisch\_rule, mp\_rule.

*)

disch_rule

//     `p`   A |- q
//   ----------------
//   A\{p} |- p ==> q

(**

| Bool.disj1\_rule                                     
-------------------

Questa &egrave; la regola di o-introduzione per il lato sinistro. Disgiunge il 
termine booleano fornito al lato destro del teorema in input.

Si veda anche: disj2\_rule, disj\_cases\_rule, mk\_disj1\_rule.

*)

disj1_rule

//    A |- p   `q`
//    ------------
//    A |- p \/ q

(**

| Bool.disj2\_rule                                     
-------------------

Questa &egrave; la regola di o-introduzione per il lato destro. Disgiunge il 
termine booleano fornito al lato sinistro del teorema in input.

Si veda anche: disj2\_rule, disj\_cases\_rule, mk\_disj1\_rule.

*)

disj2_rule

//   `p`   A |- q                                                           
//   ------------                                                           
//   A |- p \/ q      

(**

| Bool.disj\_cases\_rule                                    
-------------------

Questa &egrave; la regola di o-eliminazione. Prende un teorema di disgiunzione 
e due teoremi extra che condividono la stessa conclusione. Restituisce un 
teorema con la stessa conclusione dei teoremi extra. Le assunzioni del teorema 
restituito sono l'unione delle assunzioni dei teoremi extra, ma con il 
lato sinistro del teorema di disgiunzione rimosso dalle assunzioni del primo 
e il lato destro rimosso da quelle del secondo, e unite insieme con le 
assunzioni del teorema di disgiunzione.

Si veda anche: disj1\_rule, disj2\_rule, mk\_disj\_rule.

*)

disj_cases_rule

//  A |- p \/ q    A1 |- r    A2 |- r                                       
//  ---------------------------------                                       
//      A u A1\{p} u A2\{q} |- r     

(**

| Bool.eq\_imp\_rule1                                 
-------------------

Questa &egrave; la prima regola di eliminazione dell'equivalenza.
Prende un teorema che afferma l'equivalenza di due termini booleani, e 
restituisce un teorema che afferna che il sinistro implica il destro, 
sotto le stesse assunzioni.

Si veda anche: eq\_imp\_rule2, imp\_antisym\_rule, eq\_mp\_rule, undisch\_rule, mk\_imp\_rule.

*)

eq_imp_rule1

// A |- p <=> q
// ------------
// A |- p ==> q

(**

| Bool.eq\_imp\_rule2                                 
-------------------

Questa &egrave; la seconda regola di eliminazione dell'equivalenza.
Prende un teorema che afferma l'equivalenza di due termini booleani, e 
restituisce un teorema che afferna che il destro implica il sinistro, 
sotto le stesse assunzioni.

Si veda anche: eq\_imp\_rule1, imp\_antisym\_rule, eq\_mp\_rule, undisch\_rule, mk\_imp\_rule.

*)

eq_imp_rule2

// A |- p <=> q
// ------------
// A |- q ==> p

(**

| Wrap.eq\_mp\_rule                                
-------------------

Regola primitiva

Questa &egrave; la regola di modus ponens per l'uguaglianza. Prende un teorema di 
uguaglianza e un secondo teorema, dove il lato sinistro del teorema &egrave; 
alf-equivalente alla conclusione del secondo teorema. Restituisce un teorema che 
aggerma la parte destra del teorema di uguaglianza vale, sotto l'unione delle 
assunzioni dei teoremi forniti.

Si veda anche: mp\_rule, eq\_imp\_rule1, eq\_imp\_rule2, imp\_antisym\_rule.

*)

eq_mp_rule

//  A1 |- p <=> q    A2 |- p
//  ------------------------
//        A1 u A2 |- q


(**

| Bool.eqf\_elim\_rule                              
-------------------

Questa &egrave; la regola di eliminazione di equivalenza a falso. Prende un 
teoram di equivalenza con la `false` sulla destra, e restituisce la negazione 
logica del lato sinistro, sotto le stesse assunzioni.

Si veda anche: eqf\_intro\_rule, not\_intro\_rule, not\_elim\_rule, mk\_not\_rule,
eqt\_elim\_rule, deduct\_contrapos\_rule.

*)

eqf_elim_rule

//  A |- p <=> false                                                     
//  ----------------                                                     
//      A |- ~ p       

(**

| Bool.eqf\_intro\_rule                            
-------------------

Questa &egrave; la regola di introduzione di equivalenza a falso. Prende un 
teoram con la negazione logica come sua conclusione, e restituisce un teoram 
che afferma che il corpo della negazione &egrave; equivalente a `false`, sotto 
le stesse assunzioni.

Si veda anche: eqf\_elim\_rule, not\_elim\_rule, not\_intro\_rule, mk\_not\_rule,
eqt\_intro\_rule.

*)

eqf_intro_rule

//      A |- ~ p                                                           
//  ----------------                                                       
//  A |- p <=> false   

(**

| Bool.eqt\_elim\_rule                          
-------------------

Questa &egrave; la regola di eliminazione di equivalenza a vero. Prende un 
teoram di guguaglianza con ha `true` sul lato destro, e restituisce un 
teorema che afferma che il lato sinistro vale, sotto le stesse assunzioni.

Si veda anche: eqt\_intro\_rule, eqf\_elim\_rule.

*)

eqt_elim_rule

//  A |- p <=> true                                                       
//  ---------------                                                       
//      A |- p       

(**

| Bool.eqt\_intro\_rule                        
-------------------

Questa &egrave; la regola di introduzione di equivalenza a vero. Prende un 
qualsiasi teorema, e restituisce il teorema che afferma che la conclusione 
&egrave; equivalente a `true`, sotto le stesse assunzioni.

Si veda anche: eqt\_elim\_rule, eq\f_intro\_rule.

*)

eqt_intro_rule

//       A |- p                                                         
//  ---------------                                                     
//  A |- p <=> true      

(**

| Bool.eta\_conv                       
-------------------

Questa &egrave; la regola di eta riduzione. Prende un termine di lambda 
astrazione, dove il corpo &egrave; un'applicazione di funzione, e la variabile 
legata &egrave; il sottotermine argomento dell'applicazione della funzione e 
non &egrave; libera nel sottotermine funzione. Restituisce un teoream che 
afferma che il termine &egrave; uguale al sottotermine funzione, senza alcuna 
assunzione.

Si veda anche: beta\_conv.

*)

eta_conv

//     `\x. f x`                                                           
//  ----------------                                                       
//  |- (\x. f x) = f   


(**

| NatEval.eta\_conv                       
-------------------

Questa &egrave; la conversione di valutazione per l'addizione numerale. Prende 
un termine della forma `m + n`, dove `m` e `n` sono entrambi numeri naturali, 
e restituisce un teorema che afferma che questo equivale al suo valore numerale, 
senza assunzioni.

Si veda anche: eval\_sub\_conv, eval\_mult\_conv, eval\_exp\_conv.

*)

eval_add_conv

///    `m + n`                                                             
/// ------------                                                           
/// |- m + n = z 

(**

| NatEval.eval\_even\_conv                     
-------------------

Questa &egrave; la conversione di valutazione per la parit&agrave; per un numerale. 
Prende un termine della forma `Even n`, dove `n` &egrave; un numerale per un numero 
naturale, e restituisce un teorema che afferma il suo valore booleano, 
senza assunzioni.

Si veda anche: eval\_odd\_conv.

*)

eval_even_conv

//     `EVEN n`                                                         
// ---------------                                                      
// |- EVEN n <=> z    


(**

| NatEval.eval\_even\_conv                     
-------------------

Questa &egrave; la conversione di valutazione per l'esponenziazione numerale.
Prende un termine della forma `m EXP n`, dove `m` e `n`sono entrambi numerali 
di numeri naturali, e restituisce un teorema che afferma che questo equivale 
al suo valore, senza assunzioni.

Si veda anche: eval\_add\_conv, eval\_sub\_conv, eval\_mult\_conv.

*)

eval_exp_conv

//    `m EXP n`                                                          
// --------------                                                        
// |- m EXP n = z    

(**

| NatEval.eval\_ge\_conv                     
-------------------

Questa &egrave; la conversione di valutazione il confronto maggiore-o-uguale-a.
Prende un termine della forma `m >= n`, dove `m` e `n`sono entrambi numerali 
di numeri naturali, e restituisce un teorema che afferma che questo equivale 
al suo valore booleano, senza assunzioni.

Si veda anche: eval\_gt\_conv, eval\_le\_conv, eval\_lt\_conv, eval\_nat\_eq\_conv.

*)

eval_ge_conv

//      `m >= n`
//  ---------------
//  |- m >= n <=> z

(**

| NatEval.eval\_gt\_conv                    
-------------------

Questa &egrave; la conversione di valutazione il confronto maggiore-di.
Prende un termine della forma `m > n`, dove `m` e `n`sono entrambi numerali 
di numeri naturali, e restituisce un teorema che afferma che questo equivale 
al suo valore booleano, senza assunzioni.

Si veda anche: eval\_ge\_conv, eval\_le\_conv, eval\_lt\_conv, eval\_nat\_eq\_conv.

*)

eval_gt_conv

//      `m > n`    
//  -------------- 
//  |- m > n <=> z 

(**

| NatEval.eval\_le\_conv                    
-------------------

Questa &egrave; la conversione di valutazione per il confronto minore-o-uguale-a.
Prende un termine della forma `m <= n`, dove `m` e `n`sono entrambi numerali 
di numeri naturali, e restituisce un teorema che afferma che questo equivale 
al suo valore booleano, senza assunzioni.

Si veda anche: eval\_lt\_conv, eval\_ge\_conv, eval\_gt\_conv, eval\_nat\_eq\_conv.

*)

eval_le_conv

//        `m <= n`                               
//    --------------                            
//    |- m <= n <=> z

(**

| NatEval.eval\_le\_conv                    
-------------------

Questa &egrave; la conversione di valutazione per il confronto minore-di.
Prende un termine della forma `m < n`, dove `m` e `n`sono entrambi numerali 
di numeri naturali, e restituisce un teorema che afferma che questo equivale 
al suo valore booleano, senza assunzioni.

Si veda anche: eval\_le\_conv, eval\_ge\_conv, eval\_gt\_conv, eval\_nat\_eq\_conv.

*)

eval_lt_conv

//        `m < n`                               
//    --------------                            
//    |- m < n <=> z

(** Es. *)

"12 < 7" |> parse_term |> eval_lt_conv
// val it : thm = |- 12 < 7 <=> false

"7 < 12" |> parse_term |> eval_lt_conv
// val it : thm = |- 7 < 12 <=> true

(**

| NatEval.eval\_mult\_conv                
-------------------

Questa &egrave; la conversione di valutazione per la moltiplicazione numerale. 
Prende un termine della forma `m * n`, dove `m` e `n` sono entrambi numerali di 
numeri naturali, e restituisce un teorema che afferma che questo equivale al 
suo valore numerale, senza assunzioni.

Si veda anche: eval\_add\_conv, eval\_sub\_conv, eval\_exp\_conv.

*)

eval_mult_conv

//     `m * n`                                                            
//  ------------                                                          
//  |- m * n = z

(** Es. *)

"12 * 7" |> parse_term |> eval_mult_conv
// val it : thm = |- 12 * 7 = 84

(**

| NatEval.eval\_nat\_eq\_conv                   
-------------------

Questa &egrave; la conversione di valutazione per l'eguaglianza numerica. 
Prende un termine della forma `m = n`, dove `m` e `n` sono entrambi numerali di 
numeri naturali, e restituisce un teorema che afferma che questo equivale al 
suo valore booleano, senza assunzioni.

Si veda anche: eval\_le\_conv, eval\_lt\_conv, eval\_ge\_conv, eval\_gt\_conv.

*)

eval_nat_eq_conv

//      `m = n`                                                            
//  --------------                                                         
//  |- m = n <=> z   

(**

| NatEval.eval\_odd\_conv                   
-------------------

Questa &egrave; la conversione di valutazione per la disparit&agrave; numerale. 
Prende un termine della forma `ODD n`, dove `n` &egrave; un numerale di un numero 
naturale, e restituisce un teorema che afferma il suo valore booleano, senza 
assunzioni.

Si veda anche: eval\_even\_conv.

*)

eval_odd_conv

//      `ODD n`                                                            
//  --------------                                                         
//  |- ODD n <=> z 


(**

| NatEval.eval\_pre\_conv                  
-------------------

Questa &egrave; la conversione di valutazione per il predcessore numerale. Prende 
un termine della forma `PRE n`, dove `n` &egrave, un numerale di un numero naturale, 
e restituisce un teorema che afferma che questo equivale al suo valore numerale, 
senza assunzioni.

Si veda anche: eval\_suc\_conv.

*)

eval_pre_conv

//     `PRE n`                                                         
//  ------------                                                       
//  |- PRE n = z   

(**

| NatEval.eval\_sub\_conv                  
-------------------

Questa &egrave; la conversione di valutazione per la sottrazione numerale. Prende 
un termine della forma `m - n`, dove `m` e `n` sono entrambi numerali di numeri 
naturali, e restituisce un teorema che afferma che questo equivale al suo 
valore numerale, senza assunzioni.

Si veda anche: eval\_add\_conv, eval\_mult\_conv, eval\_exp\_conv.

*)

eval_sub_conv

//     `m - n`                                                         
//  ------------                                                       
//  |- m - n = z  


(**

| NatEval.eval\_sub\_conv                  
-------------------

Questa &egrave; la conversione di valutazione per il successore numerale. Prende 
un termine della forma `SUCC n`, dove `n` &egrave; un numerale per un numero naturale, 
e restituisce un teorema che afferma che questo equivale al suo valore numerale, 
senza assunzioni.

Si veda anche: eval\_add\_conv, eval\_mult\_conv, eval\_exp\_conv.

*)

eval_suc_conv

//     `SUC n`                                                            
//  ------------                                                          
//  |- SUC n = z     

(**

| BoolClass.eval\_sub\_conv                  
-------------------

Questa &egrave; di introduzione del quantificatore esistenziale. Prende 
un termine esistenziale, un termine testimone, e un teorema, dove la conclusione 
del teorea &egrave; il corpo del termine esistenziale ma con il termine testimone 
che sostituisce le occorrenze della sua variabile legata. Restituisce un teorema 
che afferma che il termine esistenziale fornito vale, sotto le stesse 
assunzioni del teorema fornito.

Si veda anche: choose\_rule, select\_rule, mk\_exists\_rule.

*)

exists_rule

//  `?x. p`   `t`   A |- p[t/x]                                            
//  ---------------------------                                            
//          A |- ?x. p    

(**

| Bool.gen\_rule                  
-------------------

Questa &egrave; di introduzione del quantificatore universale. Quantifica 
universamente il teorema fornito con la variabile legata fornita sotto le 
stesse assunzioni. La variabile legata non deve comparire libera nelle 
assunzioni.

Si veda anche: list\_gen\_rule, spec\_rule, mk\_forall\_rule.

*)

gen_rule

// `x`   A |- p         [ "x" not free in `A` ]                           
// ------------                                                           
//  A |- !x. p        


(**

| Bool.imp\_antisym\_rule                  
-------------------

Questa &egrave; la regola di antisimmetria per l'implicazione. Prende due 
teoremi di implicazione come argomenti, dove il lato sinistro di ciascuno 
&egrave; lo stesso (modulo alfa-equivalenza) del lato destro dell'altro. 
Restituisce 

Si veda anche: list\_gen\_rule, spec\_rule, mk\_forall\_rule.

*)

imp_antisym_rule

//   A1 |- p ==> q    A2 |- q ==> p                                       
//   ------------------------------                                       
//         A1 u A2 |- p <=> q   

(**

| Bool.imp\_trans\_rule                 
-------------------

Questa &egrave; la regola di transitivt&agrave; per l'implicazione. Prende due 
teoremi d'implicazione come argomenti, dove il lato destro del primo teorema 
&egrave; lo stesso (modulo alfa-equivalenza) del lato sinistro del secondo. 
Restituisce un teorema che afferma che il lato sinistro del primo teorema 
implica il lato destro del secondo, sotto l'unione delle assunzione dei due 
teoremi.

Si veda anche: list\_imp\_trans\_rule, eq\_trans\_rule, disch\_rule, imp\_anitsym\_asm\_rule.

*)

imp_trans_rule

//  A1 |- p ==> q    A2 |- q ==> r                                        
//  ------------------------------                                        
//        A1 u A2 |- p ==> r        

(**

| Wrap.inst\_rule                 
-------------------

Regola primitiva

Questa &egrave; la regola d'istanziazione della variabile. Prende una lista di 
instanziazioni di variabili e un teorema, ed esegue una singola instanziazione 
parallela delle variabili libere nelle assunzioni e nella conclusione del teorema, s
econdo la lista di instanziazioni. Tutte le occorrenze libere di elementi nel dominio 
della lista di instanziazione sono sostituite nel teorema. Ciascun elemento del dominio 
della lista di instanziazione deve essere una variabile, e ciascun elemento nel rango 
deve avere lo stesso tipo del corrispondente elemento del dominio.

Le variabili legate nel teorema risultante sono rinominate a seconda delle 
necessit&agrave; per evitare catture di variabili. Si noti che gli elementi della 
lista che non possono essere applicati sono semplicemente ignorati, cos&igrave; 
come lo sono gli elementi ripetuti per una data variabile (oltre al primo elemento). 
Se nessun elemento della lista soddisfa i criteri, allora il teorema risultante 
&egrave; lo stesso del teorema in input.

Si veda anche: inst\_type\_rule, subs\_rule, subst\_rule.

*)

inst_rule

//       [(x1,t1);(x2,t2);..]    A |- p
//   --------------------------------------
//   A[t1/x1,t2/x2,..] |- p[t1/x1,t2/x2,..]


(**

| Wrap.inst\_type\_rule                 
-------------------

Regola primitiva

Questa &egrave; la regola d'istanziazione delle variabili di tipo. Prende una lista di 
instanziazioni di variabili di tipo e un teorema, ed esegue una singola instanziazione 
parallela delle variabili di tipo nelle assunzioni e nella conclusione del teorema, secondo 
la lista di instanziazione. Tutte le occorrenze di elementi nel dominio della lista 
di instanziazione sono sostituite nel teorema. Ciascun elemento del dominio della 
lista deve essere una variabile di tipo.

Le variabili legate nel teorema risultante sono rinominate a seconda delle 
necessit&agrave; per evitare catture di variabili. Si noti che gli elementi della 
lista che non possono essere applicati sono semplicemente ignorati, cos&igrave; 
come lo sono gli elementi ripetuti per una data variabile (oltre al primo elemento). 
Se nessun elemento della lista soddisfa i criteri, allora il teorema risultante 
&egrave; lo stesso del teorema in input.

Si veda anche: inst\_rule.

*)

inst_type_rule

//        [(tv1,ty1);(tv2,ty2);..]    A |- p
//   ----------------------------------------------
//   A[ty1/tv1,ty2/tv2,..] |- p[ty1/tv1,ty2/tv2,..]

(**

| Bool.inst\_rule                 
-------------------

...

Si veda anche: gen_rule, list_spec_rule.

*)

list_gen_rule

(**

| Bool.list\_imp\_trans\_rule            
-------------------

...

Si veda anche: imp\_trans\_rule.

*)

list_imp_trans_rule

(**

| Bool.list\_spec\_rule          
-------------------

Questa &egrave; la regola di eliminazine universale composta. Spoglia il 
quantificatore universale pi&ugrave; esterno del teorema fornito per 
ogni elemento nella lista di termini fornita, sostituendo nel corpo ciascuna 
occorrenza di una variabile legata eliminata con il corrispondente elemento 
nella lista di termini. Il tipo di ogni termine nella lista deve essere 
uguale al tipo della sua corrispondente variabile.

Si veda anche: spec\_rule, spec\_all\_rule, bspec\_rule, list\_gen\_rule.

*)

list_spec_rule

//  [`t1`;`t2`;..]   A |- !x1 x2 .. . p                                   
//  -----------------------------------                                   
//         A |- p[t1/x1;t2/x2;..]    

(**

| Wrap.mk\_abs\_rule                
-------------------

Regola primitiva

Questa &egrave; la regola di congruenza di eguaglianza per la lambda astrazione.
Prende una variabile e un teorema di uguaglianza, e astrae la variabile da 
entrambi i lati del teorema. La variabile non deve occorrere libera nelle 
assunzioni del teorema fornito.


Si veda anche: mk\_comb\_rule.

*)

mk_abs_rule

//      `x`   A |- t1 = t2        [ "x" not free in 'A' ]
//   ------------------------
//   A |- (\x. t1) = (\x. t2)


(**

| EqCong.mk\_bin\_rule             
-------------------

Questa &egrave; la regola di congruenza di eguaglianza per l'applicazione di 
funzione binaria. Prende un termine di funzione binaria e due teoremi di 
eguaglianza, e applica la funzione nella forma curried ai corrispondenti 
lati di ciascun teorema, sotto l'unione delle loro assunzioni. Il tipo 
della funzione fornita deve avere essere binario nella forma curried, con i tipi 
del primo e del secondo dominio uguali al tipo di ciascun lato del teorema 
corrispondente.


Si veda anche: mk\_comb\_rule.

*)

mk_bin_rule

//  `f`   A1 |- s1 = s2    A2 |- t1 = t2                                  
//  ------------------------------------                                  
//      A1 u A2 |- f s1 t1 = f s2 t2    

(**

| EqCong.mk\_bin1\_rule             
-------------------

Questa &egrave; la regola di congruenza di eguaglianza per l'applicazione di 
funzione binaria sul lato sinistro. Prende un termine di funzione binaria, un 
teorema di uguaglianza e un termine, e applica la funzione in forma curried 
ai lati corrispondenti del teorema come suo lato sinistro e il termine fornito 
come lato destro. Il tipo della funzione fornita deve avere essere binario 
nella forma curried, con il tipo del primo dominio uguale al tipo di ciascun 
lato del teorema e il secondo dominio uguale al tipo del termine argomento 
aggiunto a destra.


Si veda anche: mk\_bin2\_rule, mk\_bin\_rule, mk\_comb\_rule.

*)

mk_bin1_rule

//  `f`   |- s1 = s2   `t`                                                
//  ----------------------                                                
//    |- f s1 t = f s2 t         

(**

| EqCong.mk\_bin2\_rule             
-------------------

Questa &egrave; la regola di congruenza di eguaglianza per l'applicazione di 
funzione binaria sul lato destro. Prende un termine di funzione binaria, un 
teorema di uguaglianza e un termine, e applica la funzione in forma curried 
al termine fornito sul lato sinistro e ai lati corrispondenti del teorema 
come suo lato destro. Il tipo della funzione fornita deve avere essere binario 
nella forma curried, con il tipo del primo dominio uguale al tipo del termine 
argomento a sinistra, e il tipo del secondo dominio uguale al tipo di ciascun 
lato del teorema.

Si veda anche: mk\_bin1\_rule, mk\_bin\_rule, mk\_comb\_rule.

*)

mk_bin2_rule

// `f`   `s`   |- t1 = t2                                                 
// ----------------------                                                 
//   |- f s t1 = f s t2   


(**

| Wrap.mk\_comb\_rule             
-------------------

Regola primitiva

Questa &egrave; la regola di congruenza di eguaglianza per l'applicazione di 
funzione. Prende due teoremi di equivalenza, e applica i corrispondenti lati del 
primo teoream a quelli del secondo, unendo le loro assunzioni. I lati sinistro e 
destro del primo teorema devono essere funzioni con il tipo del dominio uguale al 
tipo dei lati sinistro e destro del secondo teorema.

Si veda anche: mk\_comb1\_rule, mk\_comb2\_rule, mk\_bin\_rule, mk\_abs\_rule.

*)

mk_comb_rule

//  A1 |- f1 = f2    A2 |- t1 = t2
//  ------------------------------
//     A1 u A2 |- f1 t1 = f2 t2


(**

| Equal.mk\_comb1\_rule           
-------------------

Questa &egrave; la regola di congruenza di eguaglianza di funzioni per l'applicazione di 
funzioni. Prende un teorema di equivalenza su funzioni e un termine, e fornisce 
il termine come argomento a ciascun lato del teorema. Il tipo del termine fornito 
deve essere lo stesso del tipo del dominio delle funzioni.

Si veda anche: mk\_comb2\_rule, mk\_comb\_rule.

*)

mk_comb1_rule

//  A |- f1 = f2   `t`                                                   
//  ------------------                                                   
//   A |- f1 t = f2 t  

(**

| Equal.mk\_comb2\_rule           
-------------------

Questa &egrave; la regola di congruenza di eguaglianza di argomenti per l'applicazione di 
funzioni. Prende un termine funzione e un teorema di uguaglianza, ed applica la 
funzione a ciascun lato del teorema. Il tipo del dominio della funzione fornita deve 
essere lo stesso del tipo dei lati sinitro e destro del teorema.

Si veda anche: mk\_comb1_rule, mk\_comb\_rule.

*)

mk_comb2_rule

//  `f`   A |- t1 = t2                                                     
//  ------------------                                                     
//   A |- f t1 = f t2    


(**

| EqCong.mk\_conj\_rule         
-------------------

Questa &egrave; la regola di congruenza per la congiunzione. Prende due teoremi 
di egualianza boolena, e congiunge i corrispondenti lati del rpimo teorema 
con quelli del secondo, unendone le assunzioni.

Si veda anche: mk\_conj1\_rule, mk\_conj2\_rule, mk\_bin\_rule, conj\_rule.

*)

mk_conj_rule

//  A1 |- p1 <=> p2    A2 |- q1 <=> q2                                   
//  ----------------------------------                                   
//   A1 u A2 |- p1 /\ q1 <=> p2 /\ q2  

(**

| EqCong.mk\_conj1\_rule        
-------------------

Questa &egrave; la regola di congruenza per il lato sinistro della congiunzione. 
Prende un teorema di eguaglianza booleana e un termine booleano, e congiunge 
ciaszun lato del teorema con il termine fornito

Si veda anche: mk\_conj2\_rule, mk\_conj\_rule, mk\_bin1\_rule, conj\_rule.

*)

mk_conj1_rule

//    A |- p1 <=> p2   `q`                                                 
//  ------------------------                                               
//  A |- p1 /\ q <=> p2 /\ q     

(**

| EqCong.mk\_conj1\_rule        
-------------------

Questa &egrave; la regola di congruenza per il lato destro della congiunzione. 
Prende un termine booleano e un teorema di eguaglianza booleana, e congiunge il 
termine fornito con ciascun lato del teorema.

Si veda anche: mk\_conj1\_rule, mk\_conj\_rule, mk\_bin1\_rule, conj\_rule.

*)

mk_conj2_rule

//    `p`   A |- q1 <=> q2                                             
//  ------------------------                                           
//  A |- p /\ q1 <=> p /\ q2   

(**

| EqCong.mk\_disj\_rule        
-------------------

Questa &egrave; la regola di congruenza per la disgiunzione, Prende due 
teoremi di eguaglianza booleana, e disgiunge i corrispondenti lati del 
primo teorema con quelli del secondo, unendone le assunzioni.

Si veda anche: mk\_disj1\_rule, mk\_disj2\_rule, mk\_bin\_rule, disj1\_rule, disj2\_rule.

*)

mk_disj_rule

//  A1 |- p1 <=> p2    A2 |- q1 <=> q2                                   
//  ----------------------------------                                   
//   A1 u A2 |- p1 \/ q1 <=> p2 \/ q2    

(**

| EqCong.mk\_disj1\_rule       
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per la disgiunzione sul 
lato sinistro. Prende un teorema di eguaglianza booleana e un termine booleano, 
e disgiunge ogni lato del teorema con il termine fornito.

Si veda anche: mk\_disj2\_rule, mk\_disj\_rule, mk\_bin1\_rule, disj1\_rule.

*)

mk_disj1_rule

//     A |- p1 <=> p2   `q`                                                 
//   ------------------------                                               
//   A |- p1 \/ q <=> p2 \/ q  

(**

| EqCong.mk\_disj2\_rule       
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per la disgiunzione sul 
lato destro. Prende un termine booleano e un teorema di eguaglianza booleana, 
e disgiunge il termine fornito con ogni lato del teorema.

Si veda anche: mk\_disj1\_rule, mk\_disj\_rule, mk\_bin1\_rule, disj2\_rule.

*)

mk_disj2_rule

//    `p`   A |- q1 <=> q2                                             
//  ------------------------                                           
//  A |- p \/ q1 <=> p \/ q2   

(**

| EqCong.mk\_eq\_rule       
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per l'eguaglianza. 
Prende due teoremi di uguaglianza, e uguaglia i corrispondenti lati del 
primo teorema con quelli del secondo, unendone le assunzioni. I tipi di 
ciascun lato di ogni equazione devono essere uguali.

Si veda anche: mk\_eq1\_rule, mk\_eq2\_rule, mk\_eq\_rule.

*)

mk_eq_rule

//  A1 |- s1 = s2    A2 |- t1 = t2                                          
//  ------------------------------                                          
//  A1 u A2 |- s1 = t1 <=> s2 = t2  

(**

| EqCong.mk\_eq1\_rule    
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per l'eguaglianza 
sul lato sinistro. Prende un teorema di uguaglianza e un termine, e uguaglia 
ogni lato del teorema con il termine fornito. Il tipo del termine fornito 
deve essere uguale al tipo di ciascun lato del teorema fornito.

Si veda anche: mk\_eq2\_rule, mk\_eq\_rule, mk\_eq1\_rule.

*)

mk_eq1_rule

//   A |- s1 = s2   `t`                                                   
// ----------------------                                                 
// A |- s1 = t <=> s2 = t  

(**

| EqCong.mk\_eq2\_rule     
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per l'eguaglianza 
sul lato destro. Prende un termine e un teorema di eguaglianza, e uguaglia 
il termine a ciascun lato del teorema. Il tipo del termine fornito deve 
essere uguale al tipo di cascun lato del teorema fornito.

Si veda anche: mk\_eq1\_rule, mk\_eq\_rule, mk\_eq1\_rule.

*)

mk_eq2_rule

//    `s`   A |- t1 = t2                                                   
//  ----------------------                                                 
//  A |- s = t1 <=> s = t2    

(**

| EqCong.mk\_exists\_rule    
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per la quantificazione 
esistenziale. Prende una variabile e un teorema di uguaglianza, e quantifica 
in modo esistenzaiale la variabile su entrambi i lati del teorema. La variabile 
non deve occorrere libera nelle assunzioni del teorema fornito

Si veda anche: mk\_uexists\_rule, mk\_abs\_rule, mk\_comb\_rule, exists\_rule.

*)

mk_exists_rule

//     `x`   A |- p1 <=> p2         [ "x" not free in `A` ]                
//  --------------------------                                             
//  A |- (?x. p1) <=> (?x. p2)  


(**

| EqCong.mk\_forall\_rule  
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per la quantificazione 
universale. Prende una variabile e un teorema di uguaglianza, e quantifica 
universalmente la variabile su entrambi i lati del teorema. La variabile 
non deve occorrere libera nelle assunzioni del teorema fornito

Si veda anche: mk\_abs\_rule, mk\_comb\_rule, gen\_rule.

*)

mk_forall_rule

//     `x`   A |- p1 <=> p2         [ "x" not free in `A` ]              
//  --------------------------                                           
//  A |- (!x. p1) <=> (!x. p2)    

(**

| EqCong.mk\_imp\_rule 
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per l'implicazione. 
Prende due teoremi di eguaglianza booleana, e crea l'implicazione dai 
corrispondeti lati del primo e del secondo teorema, unendone le assunzioni.

Si veda anche: mk\_imp1\_rule, mk\_imp2\_rule, mk\_bin\_rule.

*)

mk_imp_rule

//  A1 |- p1 <=> p2    A2 |- q1 <=> q2                                    
//  ----------------------------------                                    
//  A1 u A2 |- p1 ==> q1 <=> p2 ==> q2 


(**

| EqCong.mk\_imp1\_rule 
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per l'implicazione 
su lato sinistro. Prende un teorema di eguaglianza booleana e un termine 
booleano, e crea le implicazioni da ogni lato del teorema, con il lato 
del teorema come antecedente e il termine come conseguente.

Si veda anche: mk\_imp2\_rule, mk\_imp\_rule, mk\_bin1\_rule

*)

mk_imp1_rule

//    A |- p1 <=> p2   `q`                                               
// --------------------------                                            
// A |- p1 ==> q <=> p2 ==> q    

(**

| EqCong.mk\_imp2\_rule 
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per l'implicazione 
su lato destro. Prende un termine booleano e un teorema di eguaglianza 
booleana, e rende il termine un antecedente di ciascun lato del teorema.

Si veda anche: mk\_imp1\_rule, mk\_imp\_rule, mk\_bin2\_rule

*)

mk_imp2_rule

//    `p`   A |- q1 <=> q2                                            
//  --------------------------                                        
//  A |- p ==> q1 <=> p ==> q2  


(**

| EqCong.mk\_not\_rule 
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per la negazione 
logica, Prende un teorema di eguaglianza booleana, e nega logicamente 
ciascun lato del teorema.

Si veda anche: mk\_comb\_rule, eqf\_intro\_rule, eqf\_elim\_rule.

*)

mk_not_rule

//    A |- p1 <=> p2                                                      
//  ------------------                                                    
//  A |- ~ p1 <=> ~ p2   

(**

| Pair.mk\_pair\_rule
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per l'accoppiamento.
Prende due teoremi di uguaglianza, e accoppia i corrispondenti lati del 
primo teorema con quelli del secondo, unendone le assunzioni

Si veda anche: mk\_pair1\_rule, mk\_pair2\_rule, mk\_bin\_rule.

*)

mk_pair_rule

//  A1 |- x1 = x2    A2 |- y1 = y2                                       
//  ------------------------------                                       
//   A1 u A2 |- (x1,y1) = (x2,y2)    

(**

| Pair.mk\_pair1\_rule
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per la coppia a 
sinistra. Prende un teorema di uguaglianza e un termine, e accoppia ogni 
lato del teorema con il termine.

Si veda anche: mk\_pair2\_rule, mk\_pair\_rule, mk\_bin1\_rule.

*)

mk_pair1_rule

//    A |- x1 = x2   `y`                                                  
//   --------------------                                                 
//   A |- (x1,y) = (x2,y) 

(**

| Pair.mk\_pair2\_rule
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per la coppia a 
destra. Prende un termine un teorema di uguaglianza, e accoppia il termine 
con ogni lato del teorema.

Si veda anche: mk\_pair1\_rule, mk\_pair\_rule, mk\_bin2\_rule.

*)

mk_pair2_rule

///     `x`   A |- y1 = y2                                                    
///    --------------------                                                   
///    A |- (x,y1) = (x,y2)  

(**

| EqCong.mk\_select\_rule
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per la selezione.
Prende una variabile e un teorema di eguaglianza, e seleziona la variabile 
da entrambi i lati del teorema. La variabile non deve occorrere libera 
nelle assunzioni del teorema.

Si veda anche: mk\_abs\_rule, mk\_comb\_rule.

*)

mk_select_rule

//    `x`   A |- p1 <=> p2        [ "x" not free in `A` ]                
//  ------------------------                                             
//  A |- (@x. p1) = (@x. p2)     


(**

| EqCong.mk\_uexists\_rule
-------------------

Questa &egrave; la regola di congruenza dell'eguaglianza per la quantificazione 
esistenziale univoca. Prende una variabile e un teorema di eguaglianza, e 
quantifica con quantificatore esistenziale univoco la variabile su 
entrambi i lato del teorema. La variabile non deve occorrere libera 
nelle assunzioni del teorema fornito.

Si veda anche: mk\_exists\_rule, mk\_abs\_rule, mk\_comb\_rule

*)

mk_uexists_rule

//      `x`   A |- p1 <=> p2        [ "x" not free in `A` ]               
//  ----------------------------                                          
//  A |- (?!x. p1) <=> (?!x. p2)             


(**

| Wrap.mp\_rule
-------------------

Regola primitiva

Questa &egrave; la regola di modus ponens. Prende un teorema di implicazione ed 
un secondo teorema, dove l'antecendente del teorema di implicazione &egrave; 
alfa-equivalente alla conclusione del secondo teorema. Restituisce un teorema che 
afferma che vale il conseguente del teorema di implicazione, sotto l'unione delle 
assunzioni dei teoremi forniti.

Si veda anche: eq\_mp\_rule, disch\_rule, undisch\_rule, prove\_asm\_rule.

*)

mp_rule

//   A1 |- p ==> q    A2 |- p
//   ------------------------
//         A1 u A2 |- q

(**

| Bool.not\_elim\_rule
-------------------

Questa &egrave; la regola di eliminazione della negazione logica. Prende 
un teorema di negazione logica, e restituisce un'implicazione con 
il termine negato sul lato sinistro e `false` sul lato destro, sotto le 
stesse assunzioni.

Si veda anche: not\_intro\_rule, eqf\_intro\_rule, eqf\_elim\_rule.

*)

not_elim_rule

//      A |- ~ p                                                          
//  ----------------                                                      
//  A |- p ==> false     


(**

| Bool.not\_intro\_rule
-------------------

Questa &egrave; la regola di introduzione della negazione logica. Prende un 
teorema di implicazione dove il lato destro &egrave; `false`, e restituisce la 
negazione logica del lato sinistro, sotto le stesse assunzioni.

Si veda anche: not\_elim\_rule, eqf\_elim\_rule, eqf\_intro\_rule, deduct\_contrapos\_rule.

*)

not_intro_rule

//  A |- p ==> false                                                      
//  ----------------                                                      
//      A |- ~ p     

(**

| Bool.prove\_asm\_rule
-------------------

Questa &egrave; la regola di assunzione provata. Prende due teoremi, e 
restituisce il secondo teorema ma con la conclusione del primo teorema 
rimossa (se presente) dalle sue assunzioni a cui sono aggiunte le assunzioni 
del primo teorema. Si noti che la conclusione del primo teorema non deve 
essere nelle assunzioni del secondo affinch&egrave; questa regola abbia 
successo.

Si veda anche: mp\_rule, undisch\_rule.

*)

prove_asm_rule

//  A1 |- p    A2 |- q                                                     
//  ------------------                                                     
//  A1 u (A2\{p}) |- q   

(**

| Wrap.refl\_conv
-------------------

Regola primitiva

Questa &egrave; la regola di riflessivit&agrave; per l'uguaglianza. Prende un 
termine, e restituisce un teorema che afferma che il termine &egrave; uguale a 
se stesso, senza alcuna assunzione. Non ci sono restrizioni al termine fornito.

Si veda anche: sym\_conv, sym\_rule, trans\_rule.

*)

refl_conv

//     `t`
//  --------
//  |- t = t

(**

| BoolClass.select\_rule
-------------------

Questa &egrave; la regola di selezione esistenziale. Elimina il 
quantificatore esistenziale del teorema fornito, e sostituisce nel corpo 
ogni occorrenza della variabile legata con l'operatore di selezione 
applicato al corpo originario (con la stessa variabile legata).

Si veda anche: exists\_rule.

*)

select_rule

//     A |- ?x. p                                                         
//  ----------------                                                      
//  A |- p[(@x.p)/x]   

(**

| Bool.spec\_all\_rule
-------------------

Questa &egrave; la regola composta di eliminazione di default del quantificatore 
universale. Elimina tutti i quantificatori universali esterni dal teorema fornito. 
Si noti che il teorema fornito non deve necessariamente essere una quantificazione 
universale perch&egrave; il teorema abbia successo (in  questo caso il teorema 
risultante &egrave; semplicemente lo stesso del teorema fornito):

Si veda anche: spec\_rule, list\_spec\_rule, bspec\_rule, list\_gen\_rule.

*)

spec_all_rule

//  A |- !x1 x2 .. xn. p                                                  
//  --------------------                                                  
//         A |- p  

(**

| Equal.subs\_conv
-------------------

Questa &egrave; la conversione di sostituzione base. Prende una lista di 
teoremi di eguaglianza e un termine, e trasofrma il termine eseguendo una 
singola sostituzione parallela di tutti i suoi sottotermini liberi secondo 
i teoremi di eguaglianza. Tutto le occorrenze libere dei lati sinistri dei 
teoremi di eguaglianza nel termine vegono rimpiazzate. Il teorema risultante 
ha l'unione delle assunzioni di tutti i teoremi forniti (indipendentemente 
dal fatto che esse si applichino al teorema).

Le variabili legate nel lato destro del teorema risultante sono rinominate 
a seconda delle necessit&agrave; per evitare catture di variabili. Si noti 
che se uno dei lati sinistri dei teorei di uguaglianza occorre libero 
in uno degli altri, allora viene usato di preferenza il teorema con il lato 
sinistro pi&ugrave; ampio, e se due teoremi di uguaglianza hanno lati sinistri 
alfa-equivalenti, allora di preferenza &egrave; usato di preferenza il primo 
teorema nella lisa. Se nessuno dei teoremi di eguaglianza pu&ograve; essere 
usato, allora il lato destro del teorema risultante &egrave; lo stesso del 
suo lato sinistro.

Si veda anche: subs\_rule, subst\_conv, inst\_rule.

*)

subs_conv

//    A1 |- s1 = t1   A2 |- s2 = t2   ..   `t`                               
//    ----------------------------------------                               
//     A1 u A2 u .. |- t = t[t1/s1,t2/s2,..]  

(**

| Equal.subs\_rule
-------------------

Questa &egrave; la regola di sostituzione di base. Prende una lista di 
teoremi di equivalenza e un teorema, ed esegue una singola sostituzione 
parallela dei sottotermini liberi nella conclusione del teorema secondo i 
teoremi di equivalenza. Tutte le occorrenze libere dei lati sinistri dei 
teoremi di equivalenza nel teorema vengono rimpiazzate. Il teorema risultante 
ha l'unione di tutte le assunzioni di tutti i teoremi forniti (indipendentemente 
dal fatto che questi si applichino o meno al teorema fornito).

Le variabili legate nel teorema risultante sono rinominate 
a seconda delle necessit&agrave; per evitare catture di variabili. Si noti 
che se uno dei lati sinistri dei teorei di uguaglianza occorre libero 
in uno degli altri, allora viene usato di preferenza il teorema con il lato 
sinistro pi&ugrave; ampio, e se due teoremi di uguaglianza hanno lati sinistri 
alfa-equivalenti, allora di preferenza &egrave; usato di preferenza il primo 
teorema nella lisa. Se nessuno dei teoremi di eguaglianza pu&ograve; essere 
usato, allora la conclusione del teorema risultante &egrave; la stessa 
dell'input.

Si veda anche: subs\_conv, subst\_rule, inst\_rule.

*)

subs_rule

//  A1 |- s1 = t1   A2 |- s2 = t2   ..    A |- t                           
//  --------------------------------------------                           
//       A1 u A2 u .. |- t[t1/s1,t2/s2,..]  

(**

| Equal.subst\_conv
-------------------

Questa &egrave; la conversione di sostituzione tramite template. Prende uno 
schema di sostituzione (nella forma di una lista di associazione e un termine 
template) seguito da un termine principale, e trasforma il termine principale 
una singola sostituzione parallela di tutti i suoi sottotermini liberi, secondo 
lo schema di sostituzione. Il termine template determina quali occorrenze 
libere dei lati sinistri del teorema di equivalenz nel termine principale sono 
rimpiazzate, e riflette la struttura sintattica del termine, eccetto che per 
l'avere atomi variabili template al posto dei sottotoermini a causa del 
rimpiazzamento. La lista di associazione mappa ogni variabile template a un 
teorema di equivalenza, con il lato sinistro del teorema di equivalenza per 
il sottotermine del termine principale originale e il lato destro per il 
sottotermine che lo rimpiazza. Il teorema risultante ha l'unione delle 
assunzioni di tutti i teoremi forniti (indipenentemente dal fatto che essi 
si applichino al template fornito).

Le variabili legate nel teorema risultante sono rinominate secondo le 
necessit&agrave; per evitare catture di variabili. Si noti che se due elementi 
appaiono nella lista di associazione per la stessa variabile template, allora 
viene usato il primo elemento, e che elementi per variabili che non appaiono 
nel template sono ignorate. Se nessun elemento pu&ograve; essere applicato, 
allora il lato destro della conclusione del teorema risultante &egrave; 
lo stesso del suo lato sinistro.

Si veda anche: subst\_rule, subs\_conv, inst\_rule.

*)

subst_conv

//     `v1`           `v2`          ..                                     
//  A1 |- s1 = t1   A2 |- s2 = t2   ..   `t`   `t[s1/v1,s2/v2,..]`         
//  --------------------------------------------------------------         
//      A1 u A2 u .. |- t[s1/v1,s2/v2,..] = t[t1/v1,t2/v2,..]     

(**

| Equal.subst\_rule
-------------------

Questa &egrave; la regola di sostituzione tramite template. Prende uno 
schema di sostituzione (nella forma di una lista di associazione e di 
un termine template) seguito da un teorema, ed esegue una singola sostituzione 
parallela di tutti i sottotermini liberi nella conclusione del teorema, secondo 
lo schema di sostituzione. Il termine template determina quali occorrenze 
libere dei lati sinistri del teorema di equivalenza vengono rimpiazzate nella 
conclusione del teorema, eccetto che variabili atomiche template al posto 
dei sottotermini a causa del rimpiazzamento. La lista di associazione mappa 
ogni variabile template a un teorema di equivalenza, con il lato sinistro del 
teorema di equivalenza per il sottotermine del teorema originale fornito e il 
lato destro per il sottotermine che viene sostituito. Il teorema risultante 
ha l'unione delle assunzioni di tutti i teoremi forniti (indipenentemente dal 
fatto che essi si applichino al template fornito).

Le variabili di astrazione nel teorema risultante sono rinominate secondo le 
necessit&agrave; per evitare catture di variabili. Si noti che se due elementi 
appaiono nella lista di associazione per la stessa variabile template, allora 
viene usato il primo elemento, e che elementi per variabili che non appaiono 
nel template sono ignorate. Se nessun elemento pu&ograve; essere applicato, 
allora il lato destro della conclusione del teorema risultante &egrave; 
lo stesso del suo lato sinistro.

Si veda anche: subst\_conv, subs\_rule, inst\_rule.

*)

subst_rule

//     `v1`            `v2`          ..                                      
//   A1 |- s1 = t1   A2 |- s2 = t2   ..   `t`   A |- t[s1/v1,s2/v2,..]       
//   -----------------------------------------------------------------       
//                  A1 u A2 u .. |- t[t1/v1,t2/v2,..]     

(**

| Bool.sym\_conv
-------------------

Questa &egrave; la conversione di simmetria per l'uguaglianza. Trasforma il 
termine di ugualianza fornito scambiando il lato sinistro con il destro, senza 
alcuna assunzione.

Si veda anche: sym\_rule, refl\_conv.

*)

sym_conv

//          `t1 = t2`                                                      
//   ----------------------                                                
//   |- t1 = t2 <=> t2 = t1      

(**

| Equal.sym\_conv
-------------------

Questa &egrave; la regola di simmetria per l'uguaglianza. Scambia il lato 
sinistro con il destro nel teorema di uguaglianza fornito.

Si veda anche: sym\_conv, refl\_conv, trans\_rule.

*)

sym_rule

//  A |- t1 = t2                                                           
//  ------------                                                           
//  A |- t2 = t1

(**

| Equal.trans\_rule
-------------------

Questa &egrave; la regola di transitivit&agrave; per l'uguaglianza. Prende 
due teoremi di uguaglianza, dove il lato destro del primo teorema &egrave; 
lo stesso (modulo alfa-equivalenza) del lato sinistro del secondot. Restituisce 
un teorema che afferma che il lato sinistro del primo teorema uguaglia il 
lato destro del secondo teorema, sotto l'unione delle assunzioni dei due 
teoremi.

Si veda anche: list\_trans\_rule, refl\_conv, sym\_rule, imp\_trans\_rule.

*)

trans_rule

//  A1 |- t1 = t2    A2 |- t2 = t3                                          
//  ------------------------------                                          
//        A1 u A2 |- t1 = t3    

(**

| Bool.undisch\_rule
-------------------

Questa &egrave; la regola di scaricamento. Prende un teorema di implicazione, 
e rimuove l'antecedente dalla conclusione e lo aggiunge nelle assunzioni.

Si veda anche: disch\_rule, mp\_rule, prove\_asm\_rule.

*)

undisch_rule

//  A |- p ==> q                                                           
//  ------------                                                           
//  A u {p} |- q   

(**

| Equal.conv\_rule
-------------------

...

*)

conv_rule

(**

| Equal.list\_app\_beta\_rhs\_rule
-------------------

...

*)

list_app_beta_rhs_rule

(**

| Equal.app\_beta\_rule
-------------------

...

*)

app_beta_rule

//    A |- (\v1. t1) = (\v2. t2)   `s` 
//    -------------------------------- 
//       A |- t1[s/v1] = t2[s/v2]      

(**

| Equal.list\_app\_beta\_rule
-------------------

...

*)

list_app_beta_rule
    
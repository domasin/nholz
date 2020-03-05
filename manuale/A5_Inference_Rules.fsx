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
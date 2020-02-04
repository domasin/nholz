(* ========================================================================== *)
(* DYNAMIC LOOKUP TREES (HOL Zero)                                            *)
(* - Library support for data storage in dynamic indexed binary trees         *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2012                            *)
(* ========================================================================== *)

(* ========================================================================== *)
(* F# Porting                                                                 *)
(*                                                                            *)
(* by Domenico Masini 2013                                                    *)
(* http://github.com/domasin/nholz                                        *)
(* ========================================================================== *)

/// Questo modulo costituisce una libreria di operazioni su alberi dinamici 
/// di ricerca - alberi binari auto-bilanciati che memorizzano informazioni 
/// su nodi ordinati in base a un indice rispetto alla relazione (<).
[<AutoOpen>]
module DLTree

(* Questo è implementato come alberi AA (anche chiamati alberi di Andersson), *)
(* che rimangono bilanciati con un fattore di 2 - ovvero la massima distanza  *)
(* dalla radice a una foglia non è più grande del doppio della distanza       *)
(* minima. Questo ha un'implementazione piuttosto semplice eppure è una       *)
(* delle più efficienti forme di albero binario auto-bilanciato, con ricerca, *)
(* inserimento e cancellazione che nel peggiore dei casi hanno complessità    *)
(* di tempo/spazio pari a O(log n)                                            *)

(* Alberi AA *)

(* Gli alberi AA sono una variante dei classici alberi binari di ricerca che  *)
(* mantengono una proprietà invariante aggiuntiva, chiamata "invariante AA",  *)
(* per assicurare che l'albero rimanga bilanciato all'interno di un fattore   *)
(* 2. Questa invariante usa il concetto di "livello" - un valore intero di    *)
(* misura della profonidità di un dato albero o sottoalbero.                  *)

(* L'invariante AA ha quattro aspetti:                                        *)
(* 1. Il livello di ogni foglia è 0                                           *)
(* 2. Il livello di ogni nodo sul ramo sinistro è uguale a quello del suo     *)
(*    padre meno uno                                                          *)
(* 3. Il livello di ogni nodo sul ramo destro è uguale a quello del suo       *)
(*    padre o a quello del suo padre meno uno                                 *)
(* 4. Il livello di ogni nodo sul ramo destro-destro è minore di quello dei   *)
(*    suoi nonni.                                                             *)

(* Così il livello rappresenta la distanza dal nodo alla foglia più a         *)
(* sinistra discendente dal nodo, e un limite superiore di metà della         *)
(* distanza dal nodo alla sua foglia discendente più a destra. Così il        *)
(* livello è un limite superiore di metà della profonodità dell'albero, ed è  *)
(* anche un limite superiore per la differenza tra le profondità delle foglie *)
(* più profonde e di quelle meno profonde.                                    *)

(* Le operazioni di inserimento e cancellazione preservano l'invariante AA    *)
(* applicando una combinazione di due operazioni di ribilanciamento - "skew"  *)
(* e "split" - una volta che un elemento è stato inserito/cancellato. Skew e  *)
(* split hanno entrambe una complessità tempo/spazio O(1), e il numero di     *)
(* nodi su cui hanno bisogno di operare per inserimento/cancellazione è al    *)
(* massimo O(log n), assicurando così che l'inserimento e la cancellazione    *)
(* siano O(log n). La particolare combinazione di skew e split impiegata      *)
(* dipende dal fatto che sia stata eseguita una cancellazione oppure un       *)
(* inserimento.                                                               *)

(* Si noti che per assicurare una corretta funzionalità (cioè che le voci     *)
(* possano essere cercate in base agli inserimenti e alle cancellazioni che   *)
(* sono avvenute), è sufficiente che le operazioni di inserimento e cancella- *)
(* zione preservino un corretto ordinamento rispetto a '(<)' nell'albero di   *)
(* ricerca binario classico. In altre parole, l'invariante AA è puramente per *)
(* efficienza, piuttosto che per correttezza. Si noti inoltre che le due      *)
(* operazioni di ribilanciamento preservano tutte un corretto ordinamento.    *)

(* Il datatype dltree *)

/// Il datatype 'dltree' è un datatype di albero di ricerca binario, dove ad 
/// ogni nodo sono mantenuti un indice e un elemento, e le foglie non hanno 
/// alcuna informazione. Il confronto tra indici è fatto usando la relazione 
/// di oridinamento totale polimorfica '(<)'. Ogni nodo mantiene anche un 
/// intero per il suo livello AA, per poter mantenere l'invariante AA. Si noti 
/// che non c'è alcuna necessità che le foglie mantengano il proprio livello 
/// perché esso è sempre 0.
type dltree<'a,'b> =
    | Node of int * ('a * 'b) * dltree<'a,'b> * dltree<'a,'b>
    | Leaf

//  dltree_empty : dltree<'a,'b>
//                              
/// Restituisce un nuovo dltree vuoto.
let dltree_empty = Leaf

//  dltree_elems : dltree<'a,'b> -> ('a * 'b) list                         
//                                                                         
/// Converte l'informazione mantenuta in un dato albero di ricerca 
/// binario in una lista di associazione ordinata per indice.                                   
let dltree_elems tr = 
    /// Funzione tail-ricorsiva a supporto della definizione di dltree_elems
    let rec dltree_elems0 tr xys0 =
        match tr with
        | Node (_,xy,tr1,tr2) -> dltree_elems0 tr1 (xy::(dltree_elems0 tr2 xys0))
        | Leaf                -> xys0
    dltree_elems0 tr []

(* Operazioni base sui sottoalberi *)

//  level : dltree<'a,'b> -> int
//
/// Restituisce il livello dell'albero.
let level tr =
    match tr with
    | Node (l,_,_,_) -> l
    | Leaf           -> 0

//  rightmost_elem: 'a * 'b -> dltree<'a,'b> -> 'a * 'b
//
/// Restituisce come una coppia il nodo più a destra nell'albero. 
/// Se l'albero è solo una Leaf, allora non ha nodi e in questo 
/// caso la funzione restituisce solo la coppia in input.
let rec rightmost_elem xy0 tr =
    match tr with
    | Node (_,xy,_,tr2) -> rightmost_elem xy tr2
    | Leaf              -> xy0

//  right_app: (dltree<'a,'b> -> dltree<'a,'b>) -> dltree<'a,'b> -> dltree<'a,'b>
//
/// Applica una funzione al primo nodo più a destra di un albero.
let right_app f tr =
    match tr with
    | Node (l,xy,tr1,tr2)   -> Node (l, xy, tr1, f tr2)
    | _                     -> tr

//  decrease_level: int -> dltree<'a,'b> -> dltree<'a,'b>
//
/// Decresce il livello della radice di un albero a un dato livello più basso. 
/// Se il livello dato è maggiore o uguale al livello originario l'albero rimane 
/// invariato.
let decrease_level l' tr =
    match tr with
    | Node (l,xy,tr1,tr2) when (l > l') -> Node (l',xy,tr1,tr2)
    | _  -> tr

(* skew *)

//  skew : dltree<'a,'b> -> dltree<'a,'b>
//
/// L'operazione skew esegue una singola rotazione a destra per
/// ribilanciare quando il figlio sinistro ha lo stesso livello
/// del suo padre.     
//   
//
//          D[n]                     B[n]
//         /    \                   /    \
//       B[n]  E[..]     -->     A[..]  D[n]
//      /   \                           /   \
//   A[..]  C[..]                    C[..]  E[..]
//      
let skew tr =
    match tr with
    Node (l, xy, Node (l1,xy1,tr11,tr12), tr2)
        -> if (l1 = l)
            then Node (l1, xy1, tr11, Node (l,xy,tr12,tr2))
            else tr
    | _  -> tr


(* split *)

//  split : dltree<'a,'b> -> dltree<'a,'b>
//
/// L'operazione di split esegue una singola rotazione a sinistra per  
/// ribilanciare quando il nipote destro-destro ha lo stesso livello  
/// del suo nonno, incrementando il livello del nodo radice risultante.
//     
//                                            
//        B[n]                      D[n+1]    
//       /    \                     /    \    
//    A[..]  D[n]      -->        B[n]  E[n]  
//           /  \                /   \        
//       C[..]  E[n]          A[..]  C[..]    
//
let split tr =
    match tr with
    Node (l, xy, tr1, Node (l2,xy2,tr21,tr22))
        -> if (level tr22 = l)
            then Node (l2 + 1, xy2, Node (l,xy,tr1,tr21), tr22)
            else tr
    | _  -> tr

// 	dltree_insert : ('a * 'b) -> dltree<'a,'b> -> dltree<'a,'b> when 'a : comparison             
// 	                                                                          
/// Inserisce in un dato albero di ricerca un singolo elemento indicizzato.
/// Fallisce se l'albero contiene già un entry per l'indicie fornito.      
// 	                                                                          
//  L'abero potenzialmente ha bisogno di essere ribilanciato ad ogni nodo 
//  discendente il punto d'inserimento, e questo può essere fatto da uno 
//  skew seguito da uno split.
let rec dltree_insert ((x0,_) as xy0) tr =
    match tr with
    Node (l,((x,_) as xy),tr1,tr2)
        -> let tr' = (* 1. Inserisci nell'albero, mantenendo il corretto ordinamento  *)
                    if (x0 < x)
                        then (* Inserisci nel ramo sinistro     *)
                            Node (l, xy, dltree_insert xy0 tr1, tr2)
                    else if (x < x0)
                        then (* Inserisci nel ramo destro    *)
                            Node (l, xy, tr1, dltree_insert xy0 tr2)
                        else (* L'elemento è già presente nell'albero  *) 
                            hol_fail ("dltree_insert","Already in tree") in
            let tr'' = (* 2. Ribilancia l'albero, mantenendo l'invariante AA   *)
                        (split <* skew) tr'
            tr''
    | Leaf
        -> (* Metti l'elemento qui *)
            Node (1, xy0, Leaf, Leaf)

//  dltree_delete : 'a -> dltree<'a,'b> -> dltree<'a,'b> when 'a : comparison                    
//                                                                            
/// Cancella l'entry all'indice fornito in un dato albero di ricerca. 
/// Fallisce se l'albero non contiene alcuna entry per l'indice fornito.
//  
//  L'albero potenzialmente deve essere bilanciato ad ogni nodo discendente 
//  rispetto al punto di cancellazione, e questo può essere fatto aggiustando 
//  il livello del nodo, e facendo seguire una serie di skew e poi di split.
let rec dltree_delete x0 tr =
    match tr with
    Node (l,((x,_) as xy),tr1,tr2)
        -> let tr' = (* 1. Cancella dall'albero, mantenendo l'ordinamento corretto  *)
                    if (x0 < x)
                        then (* L'elemento dovrebbe essere nel ramo sinistro *)
                            Node (l, xy, dltree_delete x0 tr1, tr2)
                    else if (x < x0)
                        then (* L'elemento dovrebbe essere nel ramo destro *)
                            Node (l, xy, tr1, dltree_delete x0 tr2)
                        else (* Il nodo contiene l'elemento che deve essere cancellato *)
                            (match (tr1,tr2) with
                                | (Leaf,_) -> tr2
                                | (_,Leaf) -> tr1
                                | _ -> let (x1,_) as xy1 = rightmost_elem xy tr1 in
                                        Node (l, xy1, dltree_delete x1 tr1, tr2)) in
            if (level tr1 < l-1) || (level tr2 < l-1)
            then (* 2. Ribilancia l'albero, per mantenere l'inviariante AA   *)
                    (right_app split <* split <*
                     right_app (right_app skew) <* right_app skew <* skew <*
                     right_app (decrease_level (l-1)) <* decrease_level (l-1)) tr'
            else tr'
    | Leaf
        -> (* L'elemento non è nell'albero *)
            hol_fail ("dltree_delete","Not in tree")

//  dltree_elem : 'a -> dltree<'a,'b> -> 'a * 'b when 'a : comparison                        
//                                                                       
/// Restituisce l'indice e l'elemento mantenuto all'indice fornito in 
/// un dato albero di ricerca. Fallisce se l'albero non ha entry per 
/// l'indice fornito.
let rec dltree_elem x0 tr =
    match tr with
    Node (_, ((x,_) as xy), tr1, tr2)
            -> if (x0 < x) then dltree_elem x0 tr1
                else if (x < x0) then dltree_elem x0 tr2
                else xy
    | Leaf -> hol_fail ("dltree_elem","Not in tree")

//  dltree_lookup : 'a -> dltree<'a,'b> -> 'b                            
//                                                                         
/// Restituisce l'elemento mantenuto all'indice fornito in un dato albero 
/// di ricerca.
let rec dltree_lookup x0 tr =
    let (_,y) = try2 (dltree_elem x0) tr "dltree_lookup" in
    y

//  dltree_mem : 'a -> dltree<'a,'b> -> bool when 'a : comparison                                
//                                                                           
/// Restituisce "true" sse l'indice fornito occorre in un dato albero di ricerca.
let rec dltree_mem x0 tr =
    match tr with
    Node (_,(x,_),tr1,tr2)
            -> if (x0 < x) then dltree_mem x0 tr1
                else if (x < x0) then dltree_mem x0 tr2
                else true
    | Leaf -> false
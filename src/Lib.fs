(* ========================================================================== *)
(* LIBRARY (HOL Zero)                                                         *)
(* - Functional programming library                                           *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2013                            *)
(* ========================================================================== *)

(* ========================================================================== *)
(* F# Porting                                                                 *)
(*                                                                            *)
(* by Domenico Masini 2013                                                    *)
(* http://github.com/domasin/nholz                                        *)
(* ========================================================================== *)

/// Questo modulo definisce varie utilità di programmazione funzionale da 
/// usare nel corso dell'implementazione.
[<AutoOpen>]                                     
module HOL.Lib

open System.Numerics
open System

//* ** GESTIONE DELL'ECCEZIONI ** *//

//* Questa sezione definisce varie funzioni di supporto per l'eccezioni,       *//
//* concentrandosi sull'eccezioni HolFail.                                     *//

//  check : ('a -> bool) -> 'a -> 'a
//  
/// Solleva un'eccezione HolFail se l'argomento fornito non soddisfa la 
/// funzione di test passata, altrimenti restituisce l'argomento.          
let check p x =
    if (p x) then x
        else hol_fail ("check","Test fails")

//  assert0 : bool -> exn -> unit 
//  
/// Solleva l'eccezione fornita se il boleano fornito è "false", 
/// altrimenti restituisce unit.                                  
let assert0 b e =
    if not b then raise e

//  assert1 : bool -> string * string -> unit                               
//                                                                         
/// Solleva un'eccezione HolFail per il nome di funzione e il messaggio forniti 
/// se il boleano fornito è "false", e altrimenti restituisce unit.
let assert1 b (func,msg) =
    if not b then hol_fail (func,msg)

//  try0 : ('a -> 'b) -> 'a -> exn -> 'b                                       
//                                                                           
/// Applica la funzione fornita all'argomento fornito, e se questo causa 
/// un'eccezione HolFail allora la gestisce e solleva l'eccezione fornita 
/// come argomento al suo posto.
let try0 f x e =
    try
        f x
    with HolFail _ -> raise e

//  try1 : ('a -> 'b) -> 'a -> string * string -> 'b                          
//                                                                           
/// Applica la funzione fornita all'argomento fornito, e se questo causa 
/// un'eccezione HolFail allora la gestisce e solleva al suo posto un'altra 
/// eccezione HolFail con il nome di funzione e il messaggio forniti.
let try1 f x (func,msg) =
    try
        f x
    with HolFail _ -> hol_fail (func,msg)

//  try2 : ('a -> 'b) -> 'a -> string -> 'b                                   
//                                                                           
/// Applica la funzinoe fornita all'argomento fornito, e se questo causa 
/// un'eccezione HolFail allora la gestisce e risolleva l'HolFail con lo 
/// stesso messaggio ma per il nome di funzione fornito.
let try2 f x func =
    try
        f x
    with HolFail (_,msg) -> hol_fail (func,msg)

//  try_find : ('a -> 'b) -> 'a list -> 'b                                   
//                                                                          
/// Applica la funzione fornita al primo elemento della lista fornita che 
/// non causa un'eccezione HolFail. Fallisce se non c'è un tale elemento nella lista.
let rec try_find f xs =
    match xs with
    | x0::xs0 -> (try f x0
                    with HolFail _ -> try_find f xs0)
    | []      -> hol_fail ("try_find","No successful application")

//  try_filter : ('a -> 'b) -> 'a list -> 'b list                         
//                                                                       
/// Applica la funzione fornita a quegli elementi della lista fornita che 
/// non causano un'eccezione HolFail, e rimuovendo quelli che lo fanno.
let rec try_filter f xs =
    match xs with
    | x0::xs0 -> let ys0 = try_filter f xs0 in
                    (try (f x0)::ys0
                     with HolFail _ -> ys0)
    | []      -> []

//  can : ('a -> 'b) -> 'a -> bool                                            
//                                                                           
/// Restituisce "true" sse applicare la funzione fornita all'argomento fornito 
/// non causa un'eccezione HolFail.
let can f x =
    try
        let _ = f x in
        true
    with HolFail _ ->
        false

//  cannot : ('a -> 'b) -> 'a -> bool                                         
//                                                                           
/// Restituisce "true" sse applicare la funzione fornita all'argomento fornito 
/// causa un'eccezione HolFail.
let cannot f x = not (can f x)

//  repeat : ('a -> 'a) -> 'a -> 'a                                           
//                                                                           
/// Applica ripetutamente la funzinoe fornita a un argomento fino a quando causa  
/// un'eccezione HolFail, restituendo la manifestazione dell'argomento che causa 
/// l'eccezione. Si noti che questa non terminerà mai se la funzione non solleva 
/// mai un'eccezione.
let rec repeat f x =
    try
        let y = f x in
        repeat f y
    with HolFail _ ->
        x

//* ** TUPLE ** *//

//* Questa sezione è per funzioni che eseguono manipolazioni di base sulle tuple.  *//

//  pair : 'a -> 'b -> 'a * 'b
//                           
/// L'operatore binario curried per costruire coppie.
let pair x y = (x,y)

//  switch : 'a * 'b -> 'b * 'a                        
//                                                    
/// Scambia tra loro i due componenti di una coppia data.
let switch (x,y) = (y,x)

//* ** LISTE ** *//

//* Questa sezione è per funzioni che eseguono manipolazioni di base sulle liste *//

/// Funzione tail recursive di supporto alla definizione di length.
let rec length0 n xs =
    match xs with
    | _::xs0 -> length0 (n+1) xs0
    | []     -> n

//  length : 'a list -> int                   
//                                           
/// Restituisce la lunghezza della lista fornita.
let length xs = length0 0 xs

//  length_big_int : 'a list -> big_int                                    
//
/// Restituisce la lunghezza della lista fornita come un intero f# 
/// di precisione arbitraria.
let length_big_int =
    let rec length0 n0 xs =
        match xs with
        | []     -> n0
        | _::xs0 -> length0 (BigInteger.Add(BigInteger.One,n0)) xs0 in
    fun xs -> length0 BigInteger.Zero xs

//  cons : 'a -> 'a list -> 'a list                                          
//
/// Aggiunge un dato elemento all'inizio di una lista data. Si tratta di 
/// una forma non infissa e curried di '::'.   
let cons x xs = x::xs

//  is_empty : 'a list -> bool                                              
//
/// Restituisce "true" sse la lista fornita è vuota.
let is_empty xs =
    match xs with
    |[] -> true
    | _ -> false

//  is_nonempty : 'a list -> bool                                              
//
/// Restituisce "true" sse la lista fornita non è vuota.
let is_nonempty xs =
    match xs with
    | [] -> false
    | _  -> true

//  hd : 'a list -> 'a                                                       
//
/// Funzione per estrarre da una lista fornita il suo elemento 
/// di testa. Fallisce se la lista è vuota.
let hd xs =
    match xs with
    | x0::_ -> x0
    | _     -> hol_fail ("hd","Empty list")

//  tl : 'a list -> 'a
//                                                                          
/// Funzione per estrarre da una lista fornita la sua coda.
/// Fallisce se la lista è vuota.
let tl xs =
    match xs with
    | _::xs0 -> xs0
    | _      -> hol_fail ("tl","Empty list")

//  hd_tl : 'a list -> 'a * 'a list                                                       
//                                                                          
/// Funzione per dividere una lista fornita nella sua testa e nella sua coda.
/// Fallisce se la lista è vuota.
let hd_tl xs =
    match xs with
    | x0::xs0 -> (x0,xs0)
    | _       -> hol_fail ("hd_tl","Empty list")

//  front : 'a list -> 'a list                                            
//                                                                       
/// Funzione per estrarre da una lista tutti gli elementi escluso l'ultimo.
/// Fallisce se la lista è vuota.
let rec front xs =
    match xs with
    | _::[]   -> []
    | x0::xs0 -> x0::(front xs0)
    | []      -> hol_fail ("front","Empty list")

//  last : 'a list -> 'a                                            
//                                                                       
/// Funzione per estrarre l'ultimo elemento di una lista fornita.
/// Fallisce se la lista è vuota.
let rec last xs =
    match xs with
    | x0::[] -> x0
    | _::xs0 -> last xs0
    | []     -> hol_fail ("last","Empty list")


//  front_last : 'a list -> 'a list * 'a                                            
//                                                                       
/// Funzione per dividere una lista fornita nei suoi primi elementi e nel suo ultimo.
/// Fallisce se la lista è vuota.
let front_last xs =
    try
        (front xs, last xs)
    with HolFail _ -> hol_fail ("front_last","Empty list")

//  list_eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool              
//                                                                         
/// Resituisce "true" sse le due liste di input sono equivalenti modulo la 
/// relazione di equivalenza fornita 'eq', cioè se le liste hanno la stessa 
/// lunghezza e gli elementi corrispondenti sono uguali secondo 'eq'.   
let rec list_eq eq xs ys =
    match (xs,ys) with
    (x0::xs0, y0::ys0) -> (eq x0 y0) && (list_eq eq xs0 ys0)
    | ([]     , []     ) -> true
    | _                  -> false

/// Funzione tail-ricorsiva a supporto della definizione di rev
let rec rev0 ys xs =
    match xs with
    x0::xs0 -> rev0 (x0::ys) xs0
    | []      -> ys

//  rev : 'a list -> 'a list                             
//                                                      
/// Inverte l'ordine degli elementi nella lista fornita.
let rev xs = rev0 [] xs

//  append : 'a list -> 'a list -> 'a list                                  
//                                                                         
/// Concatena insieme le due liste fornite. Si tratta della forma non 
/// infissa e curried di '@'
let append xs ys = xs @ ys
                                                              
//  flatten : 'a list list -> 'a list                      
//                                                        
/// Appiattisce la lista di liste fornita in una lista singola.
let rec flatten xss =
    match xss with
    xs0::xss0 -> xs0 @ (flatten xss0)
    | []        -> []                                                 

/// Funzione tail-ricorsiva a supporto della definizione di enumerate
let rec enumerate0 n xs =
    match xs with
    x0::xs1 -> (n,x0)::(enumerate0 (n+1) xs1)
    | []      -> []

//  enumerate : 'a list -> (int * 'a) list                                
//                                                                       
/// Etichetta ciascun elemento della lista fornita con la sua posizione (a base 1) 
/// nella lista.
let enumerate xs = enumerate0 1 xs

//  zip : 'a list -> 'b list -> ('a * 'b) list                               
//                                                                          
/// Combina in coppie gli elementi corrispondenti delle due liste fornite. 
/// Fallisce se le due liste non hanno la stessa lunghezza.
let rec zip xs ys =
    match (xs,ys) with
    (x0::xs0,y0::ys0) -> (x0,y0)::(zip xs0 ys0)
    | ([],[])           -> []
    | _                 -> hol_fail ("zip","Lists of unequal length")

//  unzip : ('a * 'b) list -> 'a list * 'b list                               
//                                                                           
/// Divide la lista di coppie fornita nella lista dei primi componenti 
/// e nella lista dei secondi componenti di ciascuna coppia.
let rec unzip xys =
    match xys with
    (x0,y0)::xys0 -> let (xs0,ys0) = unzip xys0 in
                        (x0::xs0,y0::ys0)
    | _             -> ([],[])

//  el : int -> 'a list -> 'a                                                
//                                                                          
/// Restituisce l'n-esimo elemento della lista fornita, usando una base 1 d'indicizzazione.
/// Fallisce se l'indice è fuori dal range.      
let rec el n xs =
    try
        if (n > 1)
            then el (n-1) (tl xs)
        else if (n = 1)
            then hd xs
            else raise LocalFail
    with HolFail _ | LocalFail ->
        if (n >= 1)
            then hol_fail ("el","Index larger than list length")
            else hol_fail ("el","Index not positive")

//  el0 : int -> 'a list -> 'a                                              
//                                                                         
/// Restituisce l'n-esimo elemento della lista fornita, usando una base 0 d'indicizzazione.
/// Fallisce se l'indice è fuori dal range.
let el0 n xs =
    try2 (el (n+1)) xs  "el0"

//  cut : int -> 'a list -> 'a list * 'a list                                 
//                                                                           
/// Divide la lista fornita in due secondo l'indice 'n' a base 1, con gli elementi 
/// da 1 a 'n' nella prima lista e i restanti nella seconda.
/// Fallisce se 'n' è negativo o maggiore della lnghezza della lista.
let rec cut n xs =
    if (n > 0)
    then match xs with
            x0::xs0 -> let (ys,zs) = cut (n-1) xs0 in
                        (x0::ys,zs)
            | _       -> hol_fail ("cut","Index larger than list length")
    else if (n = 0)
    then ([], xs)
    else hol_fail ("cut","Negative index")

/// Funzione tail-ricorsiva a supporto della definizione di cut_while
let rec cut_while0 p ys xs =
    match xs with
    x0::xs0 -> if (p x0)
                    then cut_while0 p (x0::ys) xs0
                    else (ys, xs)
    | []      -> (ys, xs)

//  cut_while : ('a -> bool) -> 'a list -> 'a list * 'a list                  
//                                                                           
/// Divide la lista fornita in due segmenti, dove il secondo segmento inizia 
/// al primo elemento che non soddisfa la funzione di test fornita.
let cut_while p xs =
    let (ys,zs) = cut_while0 p [] xs in
    (rev ys, zs)

// Compute list of all results from applying function to pairs from two lists.
/// 
/// The call allpairs f [x1;...;xm] [y1;...;yn] returns the list of results 
/// [f x1 y1; f x1 y2; ... ; f x1 yn; fx2 y1 ; f x2 y2 ...; f xm y1; 
/// f xm y2 ...; f xm yn ]
/// 
/// Never fails.
let rec allpairs f l1 l2 =
    match l1 with
    | [] -> []
    | h1 :: t1 ->
        List.foldBack (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)

(* ** NUMERI ** *)

(* Questa sezione è per funzioni che eseguono operazioni di base sui numeri.        *)


//  decrement : int -> int                                                
//
/// Sottrae 1 se l'intero fornito è positivo, altrimenti restituisce 0.
let decrement n = if (n > 0) then n-1 else 0

//  up_to : int -> int -> int list                                           
//                                                                          
/// Restituisce la lista degli interi crescenti contigui che partono dal primo 
/// intero fornito al secondo. Restituisce una lista vuota se il secondo 
/// argomento è minore del primo.
let rec up_to m n =
    if (m <= n)
    then m::(up_to (m+1) n)
    else []

(* ** LOGICA COMBINATORIA ** *)

(* Questa sezione definisce alcune funzioni classiche della logica combinatoria.      *)


//  ( <* ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b      
//                                                    
/// La funzione binaria infissa per la composizione di funzioni.
/// Corrisponde a <<.
let ( <* ) f g = fun x -> f (g x)

//  curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c                        
//
/// Restituisce l'equivalente curried di una funzione binaria che prende una coppia come argomento.
let curry f x y = f (x,y)

//  uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c                           
//
/// Restituisce l'equivalente uncurried (che prende una coppia come argomento) della 
/// funzione binaria curried passata come argomento.
let uncurry f (x,y) = f x y

//  funpow : int -> ('a -> 'a) -> 'a -> 'a                                    
//                                                                           
/// Applica l'ennesima potenza della funzione fornita. cioè esegue una 
/// ricorsione della funzione n volte, passando il risultato nuovamente come input, e
/// restituendo l'input originario se n è 0. Fallisce se la potenza è negativa.
let rec funpow n f x =
    if (n > 0)
    then funpow (n-1) f (f x)
    else if (n = 0)
    then x
    else hol_fail ("funpow","Negative power")

//  swap_arg : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c                           
//                                                                         
/// Prende una funzione binaria curried, e restituisce una funzione equivalente che 
/// prende i suoi argomenti in ordine inverso. E' chiamata il combinatore 'C' 
/// nella logica combinatoria.
let swap_arg f x y = f y x

//  dbl_arg : ('a -> 'a -> 'b) -> 'a -> 'b                                  
//                                                                         
/// Applica la funzione binaria curried fornita usando l'argomento fornito 
/// per entrambi gli argomenti della funzione. E' chiamata il combinatore 'W' 
/// nella logica combinatoria.
let dbl_arg f x = f x x

//  id_fn : 'a -> 'a                                                     
//                                                                      
/// La funzione che restituisce il suo argomento come suo risultato. E' 
/// chiamata il combinatore 'I' nella logica combinatoria.
let id_fn x = x

//  arg1_fn : 'a -> 'b -> 'a                                                
//                                                                         
/// La funzione binaria curried che restituisce il suo primo argomento. E' 
/// chiamata il combinatore 'K' nella logica combinatoria.
let arg1_fn x y = x

(* ** META FUNZIONI ** *)

(* Questa sezione è per funzioni che prendono funzioni come argomento e le applicano    *)
(* a coppie o strutture di liste                                                        *)

//  pair_apply : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd               
//                                                                          
/// Applica la coppia di funzioni fornita ai componenti corrispondenti di una coppia data                                                   
let pair_apply (f,g) (x,y) = (f x, g y)

//  map :  ('a -> 'b) -> 'a list -> 'b list                         
//                                                                 
/// Applicala funzione fornita a ciascun elemento della lista fornita.
///                                                                
///   map f [x1;x2;..;xn]  ==  [f x1; f x2; ..; f xn]
let rec map f xs =
    match xs with
    x0::xs0 -> let y = f x0 in
                y::(map f xs0)
    | []      -> []

//  map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list                 
//                                                                          
/// Applica una data funzione binaria curried agli elementi corrispondenti di due 
/// liste date. Fallisce se le liste non hanno la stessa lunghezza.
///                                                                         
///   map2 (+) [x1;x2;..;xn] [y1;y2;..;yn] = [x1 + y1; x2 + y2; ..; xn + yn]
let rec map2 f xs ys =
    match (xs,ys) with
    (x0::xs0, y0::ys0)
            -> let z = f x0 y0 in
                z::(map2 f xs0 ys0)
    | ([],[]) -> []
    | _       -> hol_fail ("map2","Lists of unequal length")

//  foldl : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b                         
//                                                                         
/// Applica l'operatore binario curried fornito sugli elementi della lista 
/// fornita, da sinistra a destra, iniziando con l'operatore applicato 
/// all'argomento extra fornito e al primo elemento della lista. Restituisce 
/// l'argomento extra se la lista è vuota.
///                                                                        
///   foldl (+) a [x1;x2;..;xn]  ==  (..((a + x1) + x2) + ..) + xn
let rec foldl f a xs =
    match xs with
    x1::xs2 -> foldl f (f a x1) xs2
    | []      -> a

//  foldl1 : ('a -> 'a -> 'a) -> 'a list -> 'a                        
//                                                                   
/// Applica l'operatore binario curried fornito sugli elementi della 
/// lista fornita, da sinistra a destra. Fallisce se la lista è vuota.
///                                                                  
///   foldl1 (+) [x1;x2;..;xn]  ==  (..(x1 + x2) + ..) + xn          
let rec foldl1 f xs =
    match xs with
    x1::xs2 -> foldl f x1 xs2
    | []      -> hol_fail ("foldl1","Empty list")

//  foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b                         
//                                                                         
/// Applica l'operatore binario curried fornito sugli elementi della 
/// lista fornita, da destra a sinistra, iniziando con l'operatore applicato 
/// all'ultimo elemento della lista e all'argomento extra fornito. Restituisce 
/// l'argomento estra se la lista è vuota.    
///                                                                        
///   foldr (+) [x1;x2;..;xn] a  ==  x1 + (x2 + (.. + (xn + a)..))
let rec foldr f xs a =
    match xs with
    x1::xs2 -> f x1 (foldr f xs2 a)
    | []      -> a

//  foldr1 : ('a -> 'a -> 'a) -> 'a list -> 'a                            
//                                                                       
/// Applica un dato operatore binario curried sugli elementi della lista 
/// fornita, da destra a sinistra. Fallisce se la lista è vuota.      
///                                                                      
///   foldr1 (+) [x1;x2;..;xn]  ==  x1 + (x2 + .. + (xn-1 + xn)..)
let rec foldr1 f xs =
    match xs with
    x::[]   -> x
    | x1::xs2 -> f x1 (foldr1 f xs2)
    | []      -> hol_fail ("foldr1","Empty list")

(* Operatori fold alternativi *)

(* Queste sono varianti banali degli operatori fold classici di sopra, più adatti   *)
(* per implementare le funzioni sintattiche di HOL (che sono uncurried).            *)

/// Versione uncurried di foldl
let foldl' mk_fn (x,xs) = foldl (curry mk_fn) x xs

/// Versione uncurried di foldr
let foldr' mk_fn (xs,x) = foldr (curry mk_fn) xs x

/// Versione uncurried di foldl1
let foldl1' mk_fn xs = foldl1 (curry mk_fn) xs

/// Versione uncurried di foldr1'
let foldr1' mk_fn xs = foldr1 (curry mk_fn) xs

/// Funzione tail-ricorsiva a supporto della definizione di unfoldl
let rec unfoldl0 dest_fn x xs =
    try
    let (x1,x2) = dest_fn x in
    unfoldl0 dest_fn x1 (x2::xs)
    with HolFail _ -> (x,xs)

//  unfoldl : ('a -> 'a * 'b) -> 'a -> 'a * 'b list                        
//                                                                        
/// Usa un dato decostruttore binario per decostruire ripetutamente il 
/// ramo sinistro dell'argomento fornito fino a quando il decostruttore 
/// causa una HolFail exception. Restituisce la parte più interna sinistra 
/// accoppiata con la lista dei rami destri.
let unfoldl dest_fn x = unfoldl0 dest_fn x []

//  unfoldl1 : ('a -> 'a * 'a) -> 'a -> 'a list                            
//                                                                        
/// Usa un dato decostruttore binario per decostruire ripetutamente il ramo 
/// sinistro dell'argomento fornito fino a quando il decostruttore casua 
/// una HolFail Exception. Restituisce la lista che inizia con il lato 
/// sinistro più interno seguito dai rami destri.
let unfoldl1 dest_fn x =
    let (x,xs) = unfoldl dest_fn x in
    x::xs 

let rec unfoldr0 dest_fn xs x =
    try
    let (x1,x2) = dest_fn x in
    unfoldr0 dest_fn (x1::xs) x2
    with HolFail _ -> (xs,x)

//  unfoldr : ('a -> 'b * 'a) -> 'a -> 'b list * 'a                         
//                                                                         
/// Usa un dato decostruttore binario per decostruire ripetutamente il lato 
/// destro dell'argomento fornito fino a quando il decostruttore cauasa una 
/// HolFail exception. Restituisce la lista dei lati sinistri, accoppiata con 
/// il lato destro più interno.
let unfoldr dest_fn x =
    let (xs,x) = unfoldr0 dest_fn [] x in
    (rev xs, x)

//  unfoldr1 : ('a -> 'a * 'a) -> 'a -> 'a list                            
//                                                                        
/// Usa un dato decostruttore binario per decostruire ripetutamente i rami 
/// destri dell'argomento fornito fino a quando il decostruttore causa una 
/// HolFail exception. Restituisce la lista dei lati sinistri e che finisce 
/// con il lato destro più interno.
let unfoldr1 dest_fn x =
    let (xs,x) = unfoldr0 dest_fn [] x in
    rev (x::xs)

/// Funzione tail ricorsiva a supporto della definizione di unfold.
let rec unfold0 dest_fn x xs =
    try
    let (x1,x2) = dest_fn x in
    unfold0 dest_fn x1 (unfold0 dest_fn x2 xs)
    with HolFail _ -> x::xs

//  unfold : ('a -> 'a * 'a) -> 'a -> 'a list                                
//                                                                          
/// Usa un dato decostruttore binario per decostruire ripetutamente tutti i 
/// rami dell'argomento fornito fino a quando il decostruttore causa una 
/// HolFail exception su ciasun sotto ramo. Restituisce una lista appiattita 
/// delle estremità risultanti.      
let unfold dest_fn x = unfold0 dest_fn x []

(* ** FUNZIONI DI TEST ** *)

(* Questa sezione è per funzioni che prendono una funzione di test (cioé una  *)
(* funzione che restituisce un booleano) come argomento                       *)

                                                                          
//  find : ('a -> bool) -> 'a list -> 'a                               
//                                                                    
/// Restituisce il primo elemento della lista fornita che soddisfa una data 
/// funzione di test. Fallisce se un tale elemento non esiste.
let rec find p xs =
    match xs with
    x0::xs0 -> if (p x0) then x0
                            else find p xs0
    | []      -> hol_fail ("find","No match")

//  filter : ('a -> bool) -> 'a list -> 'a list                       
//                                                                   
/// Rimuove tutti gli elementi della lista fornita che non soddisfano una data 
/// funzione di test.
let rec filter p xs =
    match xs with
    x0::xs0 -> if (p x0) then x0::(filter p xs0)
                            else filter p xs0
    | []      -> []

//  partition : ('a -> bool) -> 'a list -> 'a list * 'a list                
//                                                                         
/// Separa la lista fornita in due lista, per quegli elementi che rispettivamente 
/// soddisfano e non soddisfano una data funzione di test.
let rec partition p xs =
    match xs with
    x0::xs0 -> let (ys,zs) = partition p xs0 in
                if (p x0) then (x0::ys, zs)
                            else (ys, x0::zs)
    | []      -> ([], [])
                                                                         
//  exists : ('a -> bool) -> 'a list -> bool                          
//                                                                   
/// Restituisce "true" sse c'è almento un elemento nella lista fornita 
/// che soddisfa una data funzione di test.
let rec exists p xs =
    match xs with
    x0::xs0 -> (p x0) || (exists p xs0)
    | []      -> false

//  forall : ('a -> bool) -> 'a list -> bool                                 
//                                                                          
/// Restituisce "true" sse ogni elemento nella lista fornita soddisfa una data 
/// funzione di test.
let rec forall p xs =
    match xs with
    x0::xs0 -> (p x0) && (forall p xs0)
    | []      -> true

//  forall2 : ('a -> bool) -> 'a list -> 'a list -> bool                                 
//   
//  OPTIMIZE : Make this an alias for List.forall2.
/// Testa se gli elementi corrispondenti di due liste soddisfano tutte una relazionze.
let rec forall2 p l1 l2 = 
    match (l1, l2) with
    | [], [] -> true
    | (h1 :: t1, h2 :: t2) -> p h1 h2 && forall2 p t1 t2
    | _ -> false

(* ** LISTE DI ASSOCIAZIONE ** *)

(* Questa sezione è per funzioni che operano su liste di associazione. Una lista   *)
(* di associazione è una rappresentazione molto semplice di una tabella di lookup  *)
(* sotto forma di una lista di coppie. Sia il componente sinistro sia quello       *)
(* destro possono essere usati come la chiave.                                     *)

//  assoc : 'a -> ('a * 'b) list -> 'b when 'a : equality                                     
//                                                                           
/// Restituisce il componente destro della prima coppia nella lista fornita il cui 
/// componente sinistro è uguale al valore fornito. Fallisce se non può trovare una 
/// tale coppia.
let rec assoc x xys =
    match xys with
    |(x0,y0)::xys0 -> if (x = x0) then y0
                        else assoc x xys0
    | []            -> hol_fail ("assoc","No match")

//  inv_assoc : 'b -> ('a * 'b) list -> 'a when 'b : equality                                    
//                                                                           
/// Restituisce il componente sinistro della prima coppia nella lista fornita il cui 
/// componente destro è uguale al valore fornito. Fallisce se non può trovare una 
/// tale coppia.                                       
let rec inv_assoc y xys =
    match xys with
    (x0,y0)::xys0 -> if (y = y0) then x0
                        else inv_assoc y xys0
    | []            -> hol_fail ("inv_assoc","No match")

//  fst_map : ('a -> 'c) -> ('a * 'b) list -> ('c * 'b) list
//                                                         
/// Applica la funzione fornita al componente sinistro di ciascuna coppia 
/// nella lista di coppie fornita.
let fst_map f xys = map (fun (x,y) -> (f x, y)) xys

//  snd_map : ('b -> 'c) -> ('a * 'b) list -> ('a * 'c) list                 
//                                                                          
/// Applica la funzione fornita al componente destro di ciascuna coppia 
/// nella lista di coppie fornita.
let snd_map f xys = map (fun (x,y) -> (x, f y)) xys

//  fst_filter : ('a -> bool) -> ('a * 'b) list -> ('a * 'b) list             
//                                                                           
/// Elimina dalla lista di coppie fornita gli elementi con un componente 
/// sinistro che restituisce falso per la funzione di test fornita.
let fst_filter p xys = filter (fun (x,y) -> p x) xys

//  snd_filter : ('b -> bool) -> ('a * 'b) list -> ('a * 'b) list             
//                                                                           
/// Elimina dalla lista di coppie fornita gli elementi con un componente 
/// destro che restituisce falso per la funzione di test fornita.
let snd_filter p xys = filter (fun (x,y) -> p y) xys

(* ** FUNZIONI CON VALORE UNIT ** *)

(* Questa sezione è per funzioni che operano usando funzioni con valore unit. *)

//  do_map : ('a -> unit) -> 'a list -> unit                             
//                                                                      
/// Applica la funzione con valore unit fornita a turno su ciascun elemento della 
/// lista fornita, restituendo a sua volta unit.
let rec do_map f xs =
    match xs with
    x0::xs0 -> (f x0; do_map f xs0)
    | []      -> ()

(* ** INSIEMI NON ORDINATI ** *)

(* Questa sezione definisce funzioni che eseguono operazioni insiemistiche su  *)
(* liste, dove le operazioni lavorano sull'insieme di elementi che occorrono   *)
(* in una lista. Non si assume nulla circa l'ordine degli elementi o se ci     *)
(* sono ripetizioni nella lista di input, ma se un input ha degli elementi     *)
(* ripetuti, allora anche l'output potrebbe averli.                            *)

(* Per ciascuna operazione sono definite due versioni: una in cui gli elementi *)
(* sono considerati rispetto all'eguaglianza di default del linguaggio, e una  *)
(* in cui gli elementi sono considerati rispetto a una funzione di confronto   *)
(* fornita come argomento.                                                     *)


//  mem : 'a -> 'a list -> bool when 'a : equality  
//                                                              
/// Restituisce "true" sse l'elemento fornito è nella lista fornita.
let rec mem x xs =
    match xs with
    x0::xs0 -> (x = x0) || (mem x xs0)
    | []      -> false

//  mem' : ('a -> 'b -> bool) -> 'a -> 'b list -> bool           
//                                                              
/// Restituisce "true" sse l'elemento fornito è nella lista fornita rispetto 
/// a una funzione di confronto passata come argomento.
let rec mem' eq x xs =
    match xs with
    x0::xs0 -> (eq x x0) || (mem' eq x xs0)
    | []      -> false

//  insert : 'a -> 'a list -> 'a list when 'a : equality           
//                                                                        
/// Aggiunge l'elemento fornito alla lista fornita a meno che sia già nella lista.
let insert x xs =
    if (mem x xs)
    then xs
    else x::xs

//  insert' : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list           
//                                                                        
/// Aggiunge l'elemento fornto alla lista fornita a meno che sia già nella lista 
/// rispetto a una funzione di confronto fornita come argomento.
let insert' eq x xs =
    if (mem' eq x xs)
    then xs
    else x::xs

//  setify : 'a list -> 'a list when 'a : equality                       
//                                                    
/// Rimuove ogni duplicazioni di elementi dalla lista fornita.
let setify xs = rev (foldl (swap_arg insert) [] xs)

//  setify' : ('a -> 'a -> bool) -> 'a list -> 'a list 
//                                                    
/// Rimuove ogni duplicazione di elementi dalla lista fornita 
/// rispetto a una funzione di confronto fornita come argomento.
let setify' eq xs = rev (foldl (swap_arg (insert' eq)) [] xs)

//  union : 'a list -> 'a list -> 'a list when 'a : equality                                    
//                                                                         
/// Crea una lista di elementi che occorrono in almeno una delle liste fornite.
let union xs1 xs2 = foldr insert xs1 xs2

//  union' : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list                                   
//                                                                         
/// Crea una lista di elementi che occorrono in almeno una delle liste fornite 
/// rispetto a una funzione di confronto fornita come argomento.
let union' eq xs1 xs2 = foldr (insert' eq) xs1 xs2

//  unions : 'a list list -> 'a list when 'a : equality  
//                                                                       
/// Crea una lista di elementi che occorrono in almeno una delle liste all'interno  
/// della lista di liste fornita.
let unions xss =
    match xss with
    [] -> []
    | _  -> foldl1 union xss

//  unions' : ('a -> 'a -> bool) -> 'a list list -> 'a list 
//                                                                       
/// Crea una lista di elementi che occorrono in almeno una delle liste all'interno  
/// della lista di liste fornita rispetto a una funzione di confronto fornita come 
/// argomento.
let unions' eq xss =
    match xss with
    [] -> []
    | _  -> foldl1 (union' eq) xss

//  intersect : 'a list -> 'a list -> 'a list when 'a : equality    
//                                                                      
/// Crea una lista di elementi che occorrono in ciasuna delle due liste fornite.
let intersect xs1 xs2 = filter (fun x -> mem x xs2) xs1
                   
//  intersect' : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list     
//                                                                      
/// Crea una lista di elementi che occorrono in ciasuna delle due liste fornite 
/// rispetto a una funzione di confronto fornita come argomento.
let intersect' eq xs1 xs2 = filter (fun x -> mem' eq x xs2) xs1

//  subtract : 'a list -> 'a list -> 'a list when 'a : equality        
//                                                                          
/// Rimuove dalla prima lista fornita gli elmenti che occorrono anche nella 
/// seconda.
let subtract xs1 xs2 = filter (fun x1 -> not (mem x1 xs2)) xs1

//  subtract' : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list          
//                                                                          
/// Rimuove dalla prima lista fornita gli elmenti che occorrono anche nella 
/// seconda rispetto a una funzione di confronto fornita come argomento.
let subtract' eq xs1 xs2 = filter (fun x1 -> not (mem' eq x1 xs2)) xs1

//  subset : 'a list -> 'a list -> bool when 'a : equality                                      
//                                                                          
/// Restituisce "true" sse tutti gli elementi nella prima lista fornita occorrono 
/// anche nella seconda.
let subset xs1 xs2 = forall (fun x1 -> mem x1 xs2) xs1

//  subset' : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool               
//                                                                          
/// Restituisce "true" sse tutti gli elementi nella prima lista fornita occorrono 
/// anche nella seconda rispetto a una funzione di confronto fornita come argomento.                                                      
let subset' eq xs1 xs2 = forall (fun x1 -> mem' eq x1 xs2) xs1

let subset'',psubset =
    let rec subset'' l1 l2 =
        match l1, l2 with
        | [], l2 -> true
        | l1, [] -> false
        | h1 :: t1, h2 :: t2 ->
            if h1 = h2 then subset'' t1 t2
            elif h1 < h2 then false
            else subset'' l1 t2
    /// Proper subset
    and psubset l1 l2 =
        match l1, l2 with
        | l1, [] -> false
        | [], l2 -> true
        | h1 :: t1, h2 :: t2 ->
            if h1 = h2 then psubset t1 t2
            elif h1 < h2 then false
            else subset'' l1 t2
    (fun s1 s2 -> subset'' (setify s1) (setify s2)),
    (fun s1 s2 -> psubset (setify s1) (setify s2))

//  disjoint : 'a list -> 'a list -> bool                               
//                                                                     
/// Restituisce "true" sse non ci sono elementi in comune tra le due liste fornite.
let rec disjoint xs ys =
    match (xs,ys) with
    (_     , []) -> true
    | (x::xs0, _ ) -> if (mem x ys)
                        then false
                        else disjoint xs0 ys
    | ([]    , _ ) -> true

//  disjoint' : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool        
//                                                                     
/// Restituisce "true" sse non ci sono elementi in comune tra le due liste fornite 
/// rispetto a una funzione di confronto fornita come argomento.
let rec disjoint' eq xs ys =
    match (xs,ys) with
    (_     , []) -> true
    | (x::xs0, _ ) -> if (mem' eq x ys)
                        then false
                        else disjoint' eq xs0 ys
    | ([]    , _ ) -> true

//  set_eq : 'a list -> 'a list -> bool 
//                                                              
/// Restituisce "true" sse le due liste fornite hanno gli stessi 
/// elementi (senza considerare però elementi eventuali duplicati).
let set_eq xs1 xs2 = (subset xs1 xs2) && (subset xs2 xs1)
                      
//  set_eq' : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool   
//                                                              
/// Restituisce "true" sse le due liste fornite hanno gli stessi 
/// elementi (senza considerare però elementi eventuali duplicati)
/// rispetto a una funzione di confronto fornita come argomento.                     
let set_eq' eq xs1 xs2 = (subset' eq xs1 xs2) && (subset' eq xs2 xs1)

/// Funzione tail ricorsiva a supporto della definizione di no_dups
let rec no_dups0 xs0 xs =
    match xs with
    []      -> true
    | x1::xs2 -> not (mem x1 xs0) && (no_dups0 (x1::xs0) xs2)

//  no_dups : 'a list -> bool                                   
//                                                             
/// Restituisce "true" sse la lista fornita non contiene duplicati.
let no_dups xs = no_dups0 [] xs

/// Funzione tail ricorsiva a supporto della definizione di no_dups'
let rec no_dups0' eq xs0 xs =
    match xs with
    []      -> true
    | x1::xs2 -> not (mem' eq x1 xs0) && (no_dups0' eq (x1::xs0) xs2)

//  no_dups' : ('a-> 'a -> bool) -> 'a list -> bool                
//                                                             
/// Restituisce "true" sse la lista fornita non contiene duplicati
/// rispetto a una funzione di confronto fornita come argomento.
let no_dups' eq xs = no_dups0' eq [] xs

let image f s =
    setify (List.map f s)

(* ** CARATTERI E SRTINGHE ** *)

(* Questa sezione è per funzioni che operano su caratteri o stringhe.         *)


//  string_of_int : int -> string                             
//                                                           
/// Restituisce la rappresentazione sotto forma di stringa dell'intero fornito
let string_of_int = function (x:int) -> x.ToString()

//  char_implode : char list -> string              
//
/// Concatena una lista di caratteri in una singola stringa.
let char_implode (cs : char list) =
    cs |> List.fold (fun acc elem -> acc + elem.ToString()) ""

//  char_explode : string -> char list            
//                                               
/// Divide una stringa in una lista di caratteri.
let char_explode (x:string) =
    let rec foo n cs =
        if (n < 0) then cs
                else let c = x.[n] in
                        foo (n-1) (c::cs) in
    foo (String.length x - 1) []

//  implode : string list -> string                
//                                                
/// Concatena una lista di stringhe in una singola stringa.
let implode (xs:string list) =
    if (is_nonempty xs) then foldl1 (+) xs
                        else ""

//  explode : string -> string list                              
//                                                              
/// Divide una stringa in una lista di stringhe da un solo carattere.
let explode x =
    map (fun c -> c.ToString()) (char_explode x)

//  string_variant : string list -> string -> string                          
//                                                                           
/// Crea una variante della stringa fornita appendendo in fondo ad essa degli 
/// apostrofi fino a quando è diversa da ogni stringa all'interno della lista 
/// di stringhe da evitare fornita come argomento. Non appende alcun apostrofo 
/// se la stringa originale è già diversa da ognuna delle stringhe da evitare.
let rec string_variant xs0 x =
    if (mem x xs0)
    then string_variant xs0 (x + "'")
    else x

//  quote0 : string -> string                                           
//                                                                     
/// Mette degli apici singoli intorno alla stringa fornita. Non esegue 
/// alcun escape di caratteri speciali.
let quote0 x = "'" + x + "'"

let char_escape c =
    let n = c |> int in
    if (n = 34) || (n = 92)
    then char_implode ['\\'; c]
    else if (n >= 32) && (n <= 126) && not (n = 96)
    then char_implode [c]
    else let x = string_of_int n in
            match (String.length x) with
            1 -> "\\00" + x
            | 2 -> "\\0" + x
            | _ -> "\\" + x

//  quote : string -> string                                                  
//                                                                          
/// Aggiunge dei doppi-apici intorno alla stringa fornita, aggiunge dei backslash   
/// per l'escape dei backslash e dei doppi apici, e usa i codici ASCII per backquotes 
/// e caratteri non stampabili.
let quote x =
    let x1 = (implode <* (map char_escape) <* char_explode) x in
    "\"" + x1 + "\""

(* ** REPORTING ** *)

(* Questa sezione è per funzioni che emettono messaggi sullo standard output  *)


//  report : string -> unit                                                 
//                                                                         
/// Emette sullo standard output la stringa fornita come argomento preceduta 
/// dal prefisso "[HZ] " e seguita da un punto e una nuova riga. Il prefisso 
/// "[HZ] " serve a identificare i messaggi restituiti dal programma e 
/// distinguerli dai messaggi standard di .NET.
let report x = printfn "[HZ] %s." x

//  warn : string -> unit                                                    
//                                                                          
/// Emette sullo standard output la stringa fornita come argomento preceduta 
/// dal prefisso "[HZ] Warning - " e seguita da un punto e da una nuova riga.
/// Il prefisso "[HZ] Warning - " identifica i warning emessi dal programma.
let warn x = report ("WARNING: " + x)

(* ** ORDINAMENTO ** *)

(* Questa sezione è per funzioni che restituiscono liste ordinate secondo una *)
(* data funzione di ordinamento totale.                                       *)

//  merge : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list         
//                                                                     
/// Fa il merge delle due liste ordinate fornite in un'unica lista ordinata, 
/// rispetto alla relazione di ordinamento totale fornita.
let rec merge r xs ys =
    match (xs,ys) with
    (x0::xs0, y0::ys0) -> if (r x0 y0)
                            then x0::(merge r xs0 ys)
                            else y0::(merge r xs ys0)
    | (_      , []     ) -> xs
    | ([]     , _      ) -> ys

//  mergesort : ('a -> 'a -> bool) -> 'a list -> 'a list                   
//                                                                        
/// Ordina la lista fornita usando la tecnica del merge, rispetto alla 
/// relazione di orinamento totale fornita.
let mergesort r xs =
    let rec mergepairs yss xss =
        match (yss,xss) with
        ([ys], [])          -> ys
        | (_, [])             -> mergepairs [] (rev yss)
        | (_, [xs0])          -> mergepairs (xs0::yss) []
        | (_, xs1::xs2::xss3) -> mergepairs ((merge r xs1 xs2)::yss) xss3 in
    if (is_empty xs)
    then xs
    else mergepairs [] (map (fun x -> [x]) xs)

(*** From NHol ***)

let (||>>) = fun f g (x, y) -> (f x, g y)

let int_of_string (str : string) : int =
    match Int32.TryParse str with
    | true, value ->
        value
    | false, _ ->
        failwith "int_of_string"
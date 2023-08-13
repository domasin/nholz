(** 
---
title: Logica proposizionale
category: Casi di studio
categoryindex: 2
index: 1
---


Logica Proposizionale
=======================

Riferimenti
------------
In questa sezione esploriamo la logica proposizionale sfruttando il framework HOL di nholz. [Nholz](https://github.com/domasin/nholz) è semplicemente un portging in F# di [HOL Zero](http://www.proof-technologies.com/holzero/) che a sua volta è un dimostratore interattivo di teoremi sviluppato da Mark Adams in OCaml nello stile LCF della famiglia HOL.

Sfruttiamo il linguaggio definito da HolZero per esplorare la logica proposizionale con la guida dell'[Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/) di John Harrison, seguendo passo passo il capitolo sulla logica proposizionale e riaddattando le funzioni lì definite al linguaggio HOL del nostro framework. 

L'Handbook di John Harrison è accompagnato da codice sorgente in OCaml che è stato portato in F# da Eric Taucher, Jack Pappas, Anh-Dung Phan ed è disponibile su Github: [fsharp-logic-examples](https://github.com/jack-pappas/fsharp-logic-examples/). Nel ridefinire le funzioni dell'handbook riaddattandole alla logica HOL si è utilizzata come riferimento proprio l'implementazione in F# del codice descritto nell'Handbook.

Per la composizione di questa pagina si è utilizzato [F# Formatting](https://github.com/fsprojects/FSharp.Formatting/).

Introduzione
------------

La logica proposizionale studia espressioni che intendono rappresentare proposizioni, cioè affermazioni che possono essere considerate vere o false e che chiameremo nel seguito semplicemente "formule". All'interno del framework HOL che utiliziamo, queste sono semplicemente termini di tipo `bool` che possono essere costruite da atomi booleani, costituiti dalle costanti `true` e `false` e da variabili di tipo `bool`, a cui sono applicati i connettivi logici proposizionali `~`, `/\`, `\/`, `<=>` e `<=>`. Le proposizioni atomiche sono come le variabili nell'algebra ordinaria, e a volte ci riferiamo ad esse come variabili proposizionali o variabili booleane. Come suggerisce la parola "atomiche", non ne viene analizzata la struttura interna; questo porterebbe a conseiderare una logica predicativa che al momento non viene trattata. I connettivi proposizionali all'interno della logica HOL sono semplicemente funzioni da valori di verità a valori di verità.

Avvio del motore logico
------------

Per iniziare referenziamo il motore di nholz:
*)

#I "../../src/bin/Debug/net7.0/"
#r "nholz.dll"

open HOL

(** 

e istruiamo l'interprete F# a restituire una raprresentazione concreta della sintassi dei tipi e dei termini piuttosto che la loro sintassi astratta interna al sistema:

    fsi.AddPrinter print_type
    fsi.AddPrinter print_term

*)

(** 

Infine carichiamo almeno le teorie fino a `Bool` che contiene la definizione dei tipi e dei termini booleani e dei loro connettivi:

*)

CoreThry.load
Equal.load
Bool.load

(**

Operazioni sintattiche
------------

Il modulo `Bool` contiene già alcune operazioni sintattiche su formule booleane che le dividono nei loro elementi e che saranno utilizzate nel seguito.

E' necessario però definire delle nuove funzioni. Una prima cosa importante è poter distinguere tra espressioni atomiche ed esressioni composte. A questo scopo definiamo `is_bool_atom` come una funzione che restituisce vero per termini booleani costanti o variabili.

*)

/// the term is a boolean atom
let is_bool_atom tm = 
    tm |> is_bool_term && (tm |> is_const || tm |> is_var)

let pAndQ = "p /\ q" |> parse_term 
let pTerm = "p:bool" |> parse_term

printfn "%A is an atom? %b" pAndQ (pAndQ |> is_bool_atom)
printfn "%A is an atom? %b" pTerm (pTerm |> is_bool_atom)

(**
Sulle formule composte vogliamo poter applicare delle funzioni sui loro atomi. A questo scopo definiamo `overatoms` per ricorsione su termini di questo genere come un analogo dell'iteratore di liste che itera una funzione binaria su tutti gli atomi di una formula.
*)

let rec overatoms f tm b =
    if tm |> is_bool_atom then 
        f tm b
    elif tm |> is_not then
        let p = tm |> dest_not
        overatoms f p b
    elif tm |> is_conj then
        let (p,q) = tm |> dest_conj
        overatoms f p (overatoms f q b)
    elif tm |> is_disj then
        let (p,q) = tm |> dest_disj
        overatoms f p (overatoms f q b)
    elif tm |> is_imp then
        let (p,q) = tm |> dest_imp
        overatoms f p (overatoms f q b)
    elif tm |> is_eq then
        let (p,q) = tm |> dest_eq
        overatoms f p (overatoms f q b)
    else failwith "check type annotation on eq"

(**
Un'applicazione particolarmente comune è quella di raccogliere qualche insieme di attributi associati agli atomi; ritornando solamente, nel caso piùsemplice, l'insieme di tutti gli atomi. Possiamo far questo iterando una funzione f insieme con un "append" su tutti gli atomi, e convertendo infine il risultato in un insieme per rimuovere i duplicati. 
*)

let atom_union f tm =
    (tm, [])
    ||> overatoms (fun h (t) -> (f h) @ t)
    |> List.distinct |> List.sort

(**
ad esempio la possiamo utilizzare per restituire tutti gli atomi di una formula:
*)

"p /\ q"
|> parse_term
|> atom_union (fun x -> [x])

["p /\ q" |> parse_term; "p:bool" |> parse_term]
|> Seq.map (print_term)
|> fun x -> sprintf "[%s]" (x |> String.concat ", ")

(**
    val it: term list = [p:bool; q:bool]
*)


(**
La semantica della logica proposizionale
---------------------------------------

Dal momento che le formule proposizionali intendono rappresentare asserzioni che possono essere vere o false, in ultima analisi 
il significato di una formula è semplicemente uno dei due valori di verità "vero" e "falso". Comunque, esattamente 
come un'espressione algebrica x + y + 1 ha un significato definito solo quando sappiamo per che cosa stanno le variabili x e y, 
il significato di una formula proposizionale dipende dai valori di verità assegnati alle sue formule atomiche. Questa assegnazione 
è codificata in una valutazione, che è una funzione dagli insiemi degli atomi all'insieme dei valori di verità 
{falso,vero}. Data una formula `p` e una valutazione `v` valutiamo il valore di verità complessivo con la seguente funzione definita 
ricorsivamente:
*)

let rec eval tm v =
    if tm = false_tm then 
        false
    elif tm = true_tm then
        true
    elif tm |> is_bool_atom then 
        v tm
    elif tm |> is_not then 
        let p = tm |> dest_not
        not <| eval p v
    elif tm |> is_conj then 
        let (p,q) = tm |> dest_conj
        (eval p v) && (eval q v)
    elif tm |> is_disj then 
        let (p,q) = tm |> dest_disj
        (eval p v) || (eval q v)
    elif tm |> is_imp then 
        let (p,q) = tm |> dest_imp
        not(eval p v) || (eval q v)
    elif tm |> is_eq then 
        let (p,q) = tm |> dest_eq
        (eval p v) = (eval q v)
    else
        failwith "Not part of propositional logic."

(**
Questa è la nostra definizione matematica della semantica della logica proposizionale, che intende costituire una formalizzazione delle nostre intuizioni. Ogni connettivo logico è interpretato da una corrispondente funzione boolean HOL. Per essere molto espliciti sul significato di questi operatori, possiamo elencare tutte le possibili combinazioni di input e vedere gli output corrispondenti.

Possiamo presentare questa informazione in una tavola di verità che mostri come il valore di verità di una formula è determinato dalle sue sotto formule immediate.

Così per i connettivi binari avremo:

> <table class="tab">
> 	<tr>
> 		<td class="tab">p</td>
> 		<td class="tab">q</td>
> 		<td class="tab">p /\ q</td>
> 		<td class="tab">p \/ q</td>
> 		<td class="tab">p ==> q</td>
> 		<td class="tab">p <=> q</td>
> 	</tr>
> 	<tr>
> 		<td class="tab">falso</td>
> 		<td class="tab">falso</td>
> 		<td class="tab">falso</td>
> 		<td class="tab">falso</td>
> 		<td class="tab">vero</td>
> 		<td class="tab">vero</td>
> 	</tr>
>     <tr>
> 		<td class="tab">falso</td>
> 		<td class="tab">vero</td>
> 		<td class="tab">falso</td>
> 		<td class="tab">vero</td>
> 		<td class="tab">vero</td>
> 		<td class="tab">falso</td>
> 	</tr>
>     <tr>
>     	<td class="tab">vero</td>
>     	<td class="tab">falso</td>
>     	<td class="tab">falso</td>
>     	<td class="tab">vero</td>
>     	<td class="tab">falso</td>
>     	<td class="tab">falso</td>
>     </tr>
>     <tr>
>     	<td class="tab">vero</td>
>     	<td class="tab">vero</td>
>     	<td class="tab">vero</td>
>     	<td class="tab">vero</td>
>     	<td class="tab">vero</td>
>     	<td class="tab">vero</td>
>     </tr>
> </table>

e per la negazione unaria:

> <table class="tab">
> 	<tr>
> 		<td class="tab">p</td>
> 		<td class="tab">~ p</td>
> 	</tr>
> 	<tr>
> 		<td class="tab">falso</td>
> 		<td class="tab">vero</td>
> 	</tr>
>     <tr>
> 		<td class="tab">vero</td>
> 		<td class="tab">falso</td>
> 	</tr>
> </table>

Proviamo a valutare una formula "p /\ q ==> q /\ r" in una valutazione dove p, q e r sono impostati rispettivamente a "vero", "falso" e "vero". (Non ci preoccupiamo di definire il valore di atomi non coinvolti nella formula, e F# mostra un messaggio di warning che ci informa che non lo abbiamo fatto. Per evitarlo possiamo eventualmente sopprimere il warning 
avendo l'accortezza di reimpostarlo successivamente.)

*)

//#nowarn "0025";;
(function Tmvar ("p", bool_ty) -> true | Tmvar ("q", bool_ty) -> false | Tmvar ("r", bool_ty) -> true) 
|> eval (@"p /\ q ==> q /\ r" |> parse_term)
//val it : bool = true

"p /\ q ==> q /\ r"
|> parse_term
|> eval (function 
    | Tmvar ("p", bool_ty) -> true 
    | Tmvar ("q", bool_ty) -> false 
    | Tmvar ("r", bool_ty) -> true
)

(**
In un'altra valutazione, comunque, la formula viene valutata a "falso":
*)

(function Tmvar ("p", bool_ty) -> true | Tmvar ("q", bool_ty) -> true | Tmvar ("r", bool_ty) -> false) 
|> eval (@"p /\ q ==> q /\ r" |> parse_term)
//val it : bool = false

(** 

Tavole di verità meccanizzate
-------------------------

Intuitivamente sembra naturale che la valutazione di una formula sia indipendente dai valori assegnati dalla valutazione agli atomi che non occorrono nella formula. Rendiamo preciso questo concetto definendo una funzione per estrarre l'insieme delle proposizioni atomiche che occorrono in una formula, In termini matematici astratti, definiremmo atoms nel modo 
seguente per ricorsione sulle formule:

>   atoms(true)     =	{}                        <br/>
>   atoms(false)    =	{}                        <br/>
>   atoms(x)        =	{x}                       <br/>
>   atoms(~p)       =	atoms(p)                  <br/>
>   atoms(p /\ q)   =	atoms(p) U atoms(q)       <br/>
>   atoms(p \/ q)   =	atoms(p) U atoms(q)       <br/>
>   atoms(p ==> q)  =	atoms(p) U atoms(q)       <br/>
>   atoms(p <=> q)  =	atoms(p) U atoms(q)       <br/>

Per induzione strutturale sulle formule, si dimostra che atoms(p) è sempre finito e che quindi 
è possibile trattarlo in termini di liste F# (usando le liste per rappresentare insiemi).

**Teorema: Per ogni formula proposizionale p, l'insieme atoms(p) è finito.**

**Dimostrazione**. Per induzione sulla struttura della formula.

*Se p è true o false, allora atoms(p) è l'insieme vuoto, e se p è un atomo, atoms(p) è un insieme singoletto.* 
*In ogni caso, questi sono finiti.*

*Se p è della forma atoms(~ q), allora per ipotesi di induzione atoms(q) è finito* 
*e per definizione atoms(~ q) = atoms(q).*

*Se p è della forma q /\ r, q \/ r, q ==> r, q <=> r, allora atoms(p) = atoms(q) U atoms(r).* 
*Per ipotesi di induzione, sia atoms(q) che atoms(r) sono finiti, e l'unione di due insiemi finiti è un insieme finito.*

Analogamente, possiamo giustificare formalmente il fatto intuitivamente ovvio menzionato sopra che

**Teorema: Per ogni formula proposizionale p, se due valutazioni v e v' concordano sull'insieme atmos(p)
(è v(x) = v'(x) per tutti gli x in atoms(p)), allora `eval p v` = `eval p v'`.**

**Dimostrazione**. Per induzione sulla struttura della formula.

*Se p è true o false, allora è interpretata rispettivamente a true e false indipendentemente dalla assegnazione.*

*Se p è un atomo, allora atoms(x) = {x} e per assunzione v(x) = v'(x).*
*Quindi eval p v = v(x) = v'(x) = eval p v'.*

*Se p è della forma ~ q, allora allora atoms(p) = {q} e per assunzione v(x) = v'(x).*
*Quindi eval p v = not v(q) = not v'(q) = eval p v'.*

*Se p è della forma q /\ r, q \/ r, q ==> r, q <=> r, allora atoms(p) = atoms(q) U atoms(r).* 
*Dal momento che le assegnazioni si accordano sull'unione dei due insiemi, si accordano conseguentemente*
*su ognuno degli atoms(q) e atoms(r). Possiamo quindi applicare l'ipotesi di induzione per concludere che*
*eval q v = eval q v' e eval q r = eval r v'. E dal momento che la valutazione di p è una funzione*
*di queste due sottoassegnazioni, eval p v = eval p v'*.

La funzione atoms può essere implementata in F# in termini dell'iteratore `atom_union` definito di sopra:

*)

let atoms tm = 
    atom_union (fun a -> [a]) tm

(** 
per esempio:
*)

@"p /\ q ==> n = (r:bool)" |> parse_term |> atoms
//val it : term list = [n:bool; p:bool; q:bool; r:bool]

(** 
Poichè l'interpretazione di una formula proposizionale `p` dipende solo dall'azione della valutazione sull'insieme finito (diciamo di n elementi) `atoms(p)`, e può fare solo una di due scelte, il valore di verità finale è completamente determinato da tutte le 2^n scelte per questi atomi. Quindi possiamo estendere in modo naturale l'enumerazione nella forma di una tavola di verità dalle operazioni base a formule arbitrarie. Per implementare questo in F#, iniziamo definendo una funzione che testa se una funzione `subfn` ritorna true su tutte le possibili valutazioni degli atomi `ats`, usando una valutazione esistente `v` per tutti gli altri atomi. Lo spazio di tutte le valutazioni è esplorato modificando successivamente `v` in modo da impostare ogni atomo `p` a "vero" e "falso" e richiamando ricorsivamente:
*)

let rec onallvaluations subfn v ats =
    match ats with
    | [] -> subfn v
    | p :: ps ->
        let v' t q =
            if q = p then t
            else v q
        onallvaluations subfn (v' false) ps
        && onallvaluations subfn (v' true) ps

(**  
Possiamo applicare questa a una funzione che disegna una riga della tavola di verità e che ritorna "vero". 
(Il valore di ritorno è importante, perch è & valuterà il suo secondo argomento solo se il 
primo argomento è true.) Questo può quindi essere usato per disegnare l'intera tavola di verit&qgrave; per una formula:
*)

let pname tm = 
    if tm |> is_const then 
        tm |> const_name
    elif tm |> is_var then 
        tm |> var_name
    else ""

let fprint_truthtable sw fm =
    // [P "p"; P "q"; P "r"]
    let ats = atoms fm
    // 5 + 1 = length of false + length of space
    let width = List.foldBack (max << String.length << pname) ats 5 + 1
    let fixw s = s + String.replicate (width - String.length s) " "
    let truthstring p = fixw (if p then "true" else "false")
    let mk_row v =
        let lis = List.map (fun x -> truthstring (v x)) ats
        let ans = truthstring (eval fm v)
        fprintf sw "%s" (List.foldBack (+) lis ("| " + ans))
        fprintfn sw ""
        true
    let seperator = String.replicate (width * (List.length ats) + 9) "-"
    fprintfn sw "%s" (List.foldBack (fun s t -> fixw(pname s) + t) ats "| formula")
    fprintfn sw "%s" seperator
    let _ = onallvaluations mk_row (fun x -> false) ats
    fprintfn sw "%s" seperator
    fprintfn sw ""

let writeToString fn = 
    use sw = new System.IO.StringWriter()
    fn sw
    sw.ToString()

let inline print_truthtable f = fprint_truthtable stdout f
let inline sprint_truthtable f = writeToString (fun sw -> fprint_truthtable sw f)

(**
Possiamo testare la nostra funzione di stampa su alcune formule:
*)

@"p \/ ~ p" |> parse_term |> print_truthtable
//p     | formula
//---------------
//false | true  
//true  | true  
//---------------

//val it : unit = ()

@"(true ==> (x = false)) ==> ~(y \/ false /\ z)" |> parse_term |> print_truthtable
//x     y     z     false true  | formula
//---------------------------------------
//false false false false false | true  
//false false false false true  | true  
//false false false true  false | true  
//false false false true  true  | true  
//false false true  false false | true  
//false false true  false true  | true  
//false false true  true  false | true  
//false false true  true  true  | true  
//false true  false false false | false 
//false true  false false true  | false 
//false true  false true  false | false 
//false true  false true  true  | false 
//false true  true  false false | false 
//false true  true  false true  | false 
//false true  true  true  false | false 
//false true  true  true  true  | false 
//true  false false false false | true  
//true  false false false true  | true  
//true  false false true  false | true  
//true  false false true  true  | true  
//true  false true  false false | true  
//true  false true  false true  | true  
//true  false true  true  false | true  
//true  false true  true  true  | true  
//true  true  false false false | true  
//true  true  false false true  | true  
//true  true  false true  false | true  
//true  true  false true  true  | true  
//true  true  true  false false | true  
//true  true  true  false true  | true  
//true  true  true  true  false | true  
//true  true  true  true  true  | true  
//---------------------------------------

//val it : unit = ()

(*** hide ***)
//@"(true ==> (x = false)) ==> ~(y \/ false /\ z)" |> parse_term |> psimplify |> print_truthtable

(** 

Simplifying propositional formulas
-------------------------

Then I define a simplyfication function on proposition in way similar to that described by 
the John Harrison's Handbook of Automated Reasoing customized on the typed lambda language of hol.

`psimplify1` is an zusiliary function:
*)

let psimplify1 tm = 
    if tm |> is_not then 
        let tm1 = tm |> dest_not
        match tm1 with
        | Tmconst ("false", bool_ty)     -> true_tm
        | Tmconst ("true", bool_ty)      -> false_tm
        | tm1 when tm1 |> is_not         -> tm1 |> dest_not
        | _                              -> tm
    elif tm |> is_conj then              
        let (tm1,tm2) = tm |> dest_conj  
        match (tm1,tm2) with             
        | (Tmconst ("false", bool_ty),_) 
        | (_,Tmconst ("false", bool_ty)) 
                                         -> false_tm
        | (Tmconst ("true", bool_ty),p)  
        | (p,Tmconst ("true", bool_ty))  
                                         -> p
        | _                              -> tm
    elif tm |> is_disj then              
        let (tm1,tm2) = tm |> dest_disj  
        match (tm1,tm2) with             
        | (Tmconst ("false", bool_ty),p) 
        | (p,Tmconst ("false", bool_ty)) 
                                         -> p
        | (Tmconst ("true", bool_ty),_)  
        | (_,Tmconst ("true", bool_ty))  
                                         -> true_tm
        | _                              -> tm
    elif tm |> is_imp then               
        let (tm1,tm2) = tm |> dest_imp   
        match (tm1,tm2) with             
        | (Tmconst ("false", bool_ty),_) 
        | (_,Tmconst ("true", bool_ty))  
                                         -> true_tm
        | (Tmconst ("true", bool_ty),p)  -> p
        | (p,Tmconst ("false", bool_ty)) -> p |> mk_not
        | _                              -> tm
    elif tm |> is_eq then               
        let (tm1,tm2) = tm |> dest_eq   
        match (tm1,tm2) with             
        | (Tmconst ("true", bool_ty),p)  
        | (p,Tmconst ("true", bool_ty))  
                                         -> p
        | (Tmconst ("false", bool_ty),p) 
        | (p,Tmconst ("false", bool_ty)) 
                                         -> p |> mk_not
        | _                              -> tm
    else tm

(*** hide ***)
//("~ false") |> parse_term |> psimplify1
//("~ true") |> parse_term |> psimplify1
//("~ ~ x") |> parse_term |> psimplify1
//("~ x") |> parse_term |> psimplify1 

//(@"false /\ x") |> parse_term |> psimplify1 
//(@"x /\ false") |> parse_term |> psimplify1 
//(@"true /\ x") |> parse_term |> psimplify1 
//(@"x /\ true") |> parse_term |> psimplify1 

//(@"false \/ x") |> parse_term |> psimplify1 
//(@"x \/ false") |> parse_term |> psimplify1 
//(@"true \/ x") |> parse_term |> psimplify1 
//(@"x \/ true") |> parse_term |> psimplify1 

//(@"false ==> x") |> parse_term |> psimplify1 
//(@"x ==> true") |> parse_term |> psimplify1 
//(@"true ==> x") |> parse_term |> psimplify1 
//(@"x ==> false") |> parse_term |> psimplify1 

//(@"false = x") |> parse_term |> psimplify1 
//(@"x = true") |> parse_term |> psimplify1 
//(@"true = x") |> parse_term |> psimplify1 
//(@"x = false") |> parse_term |> psimplify1 

(** 
With that ready than I define `psimplify` itself:
*)

(*** unhide ***)
let rec psimplify tm =
    if tm |> is_not then
        let p = tm |> dest_not
        psimplify1 ((psimplify p) |> mk_not)
    elif tm |> is_conj then
        let (p,q) = tm |> dest_conj
        psimplify1 ((psimplify p, psimplify q) |> mk_conj)
    elif tm |> is_disj then
        let (p,q) = tm |> dest_disj
        psimplify1 ((psimplify p, psimplify q) |> mk_disj)
    elif tm |> is_imp then
        let (p,q) = tm |> dest_imp
        psimplify1 ((psimplify p, psimplify q) |> mk_imp)
    elif tm |> is_eq then
        let (p,q) = tm |> dest_eq
        psimplify1 ((psimplify p, psimplify q) |> mk_eq)
    else tm

(**
Applying the function gives the desired result:
*)

@"(true ==> (x = false)) ==> ~(y \/ false /\ z)" |> parse_term |> psimplify
//val it : term = `~ x ==> ~ y`

(** 

Valuating a formula
-------------------------

To valuate a formula, in general, I need a function that given an assignment 
to all prop variables of the formulas give me its global truth value.

Here is it:
*)

let rec onatoms f tm =
    if tm |> is_bool_term then 
        f tm
    else tm

@"a:bool" |> parse_term |> atoms
@"true" |> parse_term |> atoms
@"~p" |> parse_term |> atoms
@"~p /\ q /\ r ==> (v:bool) = x" |> parse_term |> atoms

@"a:bool" |> parse_term |> is_bool_term

let x = (@"p:bool" |> parse_term) 


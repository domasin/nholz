(**
# NHolZ

NHOLZ è il porting in F# di [HOL Zero](http://www.proof-technologies.com/holzero/): un dimostratore di teoremi nella logica HOL. Lo scopo è quello di avere un dimostratore di teoremi HOL, cioè un programma che supporta dimostrazioni formali e lo sviluppo di teorie nella logica HOL, a disposizione in F# per lo studio a livello personale di sistemi di questo tipo. Ho scelto HOL Zero come base perché, come dice il suo autore, "è un dimostratore di teoremi relativamente semplice che si concentra su buone funzionalità di base, robustezza architetturale, lo sviluppo della sintassi concreta, un prettyprinting completo e non ambiguo, e la leggibilità del codice sorgente" e perché per le sue caratteristiche è risultato piuttosto semplice effettuarne il porting. 

## Che cos'è un sistema HOL?

Un sistema HOL è un sistema informatico sviluppato per supportare la dimostrazione interattiva di teoremi nella logica di ordine superiore (da qui l'acronimo HOL per Higher Order Logic). A questo scopo, la logica formale è interfacciata da un linguaggio di programmazione di uso generale (originariamente l'ML, per meta-linguaggio, ma qui F#) in cui si possono denotare i termini e i teoremi della logica, esprimere ed applicare le strategie di dimostrazione, e sviluppare teorie logiche. 

L'idea base (derivata dall'approccio [LCF](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions)) è quella di utilizzare un *tipo di dati astratto* per i *teoremi* in modo tale, però, che 'istanze' di tale tipo siano costruibili solo a partire da un insieme di funzioni che implementano regole di inferenza logica e che tali regole siano nel loro insieme valide.

La logica di ordine superiore usata in HOL è una versione del calcolo dei predicati con i termini del lambda calcolo tipizzato (cioè la teoria semplice dei tipi). Questa fu originariamente sviluppata come una fondazione per la matematica da Church 1940<sup>[1](## 'A formulation of the simple theory of types. Journal of Symbolic Logic, 5:56–68, 1940.')</sup>.

Nello specifico la logica implementata in HOL Zero è "una logica predicativa tipizzata, classica, di ordine superiore, cioè una logica predicativa con un sistema di tipi, con la legge del terzo escluso come teorema, e con la possibilità di quantificare su funzioni."

## Avvio di una sessione

Una sessione è avviata da uno script F#. Innanzitutto è necessario referenziare la dll e importare i relativi moduli:

*)

#I "../src/bin/Debug/net7.0"
#r "nholz.dll"
open HOL

(**
impostare il pretty printing delle espressioni:
*)

fsi.AddPrinter print_type
fsi.AddPrinter print_qtype
fsi.AddPrinter print_term
fsi.AddPrinter print_qterm
fsi.AddPrinter print_thm

(**
e caricare quindi i moduli con i seguenti comandi:
*)

CoreThry.load
Equal.load
Bool.load
BoolAlg.load
BoolClass.load
Pair.load
Ind.load
Nat.load
NatNumrl.load
NatArith.load
NatRel.load
NatEval.load

(**
I primi pochi secondi di avvio richiedono il build del sistema da zero. Alcune centinaia di righe di output scorrono velocemente sullo schermo. 
*)

// ...
// [HZ] Storing theorem "sub_floor_thm".
// [HZ] Setting term fixity for name ">".
// [HZ] Declaring constant ">".
// [HZ] Adding definition for constant ">".
// [HZ] Setting term fixity for name ">=".
// [HZ] Declaring constant ">=".
// [HZ] Adding definition for constant ">=".
// val it : (string * thm) list =
//   [("eta_ax", |- !(f:'a->'b). (\x. f x) = f);
//    ("imp_antisym_ax", |- !p1 p2. (p1 ==> p2) ==> (p2 ==> p1) ==> (p1 <=> p2));
//    ("infinity_ax", |- ?(f:ind->ind). ONE_ONE f /\ ~ ONTO f);
//    ("select_ax", |- !(P:'a->bool) x. P x ==> P ($@ P))]
// 
// > 

(**

il sistema è quindi pronto per ricevere i comandi dall'utente.
Questi comandi sono di fatto espressioni F#.

## Panoramica d'uso

Questa sezione fornisce una breve introduzione a semplici operazioni, incluso come immettere espressioni HOL e come eseguire una semplice dimostrazione. 

### Termini e tipi

Le espressioni nel linguaggio HOL sono chiamati termini HOL. I termini sono scritti utilizzando una stringa di caratteri ASCII a cui va applicata la funzione `parse_term`. Nel momento in cui si immette un termine in una sessione questo viene controllato e ristampato a video.

La sintassi dei termini è semplice e intuitiva Per esempio, il seguente termine significa ''per tutti i numeri naturali `x`, `y` e `z`, se `x` è minore di `y` e `y` è minore di `z` allora `x` è minore di `z`'':

*)

@"!x y z. x < y /\ y < z ==> x < z" |> parse_term
(*** include-fsi-output ***)

(**
Se si immette un termine mal formato si riceverà un messaggio di errore.
*)

"x =" |> parse_term

// > 
// HOL.Exn+HolErr: [HZ] SYNTAX ERROR: Unexpected end of quotation instead of RHS for infix "="
// ...

(**
Si noti che i messaggi specifici del sistema, diversamente da quelli che derivano dall'interprete F#, in generale, hanno il prefisso `[HZ]'. Questo vale per tutti i messaggi riportati da NHOLZ, inclusi messaggi di errore, warnings e feedback generici all'utente.

HOL è un linguaggio tipizzato, così ogni termine e sottotermine ha un tipo, e i termini devono essere costruiti in modo da avere un tipo corretto. Questo impedisce la costruzione di enunciati privi di significato come ''3 è uguale a vero''.
*)

"3 = true" |> parse_term
// > 
// HOL.Exn+HolErr: [HZ] TYPE ERROR: Function subterm domain type incompatible with argument subterm type

(**
I sottotermini possono essere annotati per indicare il loro tipo, facendo seguire al sottotermine il simbolo di due punti `:` e poi il suo tipo, il tutto chiuso tra parentesi. Il meccanismo di inferenza del tipo è usato per risolvere i tipi nei termini. Ad ogni termine inserito senza annotazioni di tipo sufficienti sono assegnate delle variabili di tipo numerate per tutti i tipi non determinabili. Di default i termini sono ristampati indietro con solamente le annotazioni di tipo sufficienti per evitare qualsiasi ambiguità circa i tipi di ogni sottotermine.
*)

"!(w:nat) (x:nat) y z. w = x /\ y = z" |> parse_term
(*** include-fsi-output ***)

(**
I tipi HOL possono essere scritti fuori dal contesto di un termine usando la funzone `parse_type`. 
*)

"nat#nat->bool" |> parse_type
(*** include-fsi-output ***)

(**

### Teoremi, Dimostrazioni ed Asserzioni

I teoremi HOL consistono di un insieme di termini di assunzione con valore booleano e di un termine conclusione con valore booleano, e sono riservati ad enunciati di cui si è stabilito che valgono (per dimostrazione o asserzione - si veda sotto). Il significato di tali enunciati è che la conclusione vale assumendo che valgano tutte le assunzioni. I teoremi sono mostrati usando un turnstile (`|-`) per separare tutte le assunzioni dalla conclusione. Il sistema di base contiene già oltre 100 teoremi pre-dimostrati, ognuno dei quali non ha assunzione.
*)

excluded_middle_thm
(*** include-fsi-output ***)

(**
Le regole di inferenza della logica HOL sono qui implementate come funzioni F# che prendono teoremi e/o termini e restituiscono teoremi. Un passo di dimostrazione è eseguito semplicemente valutando l'applicazione di una tale funzione.
*)

"x + y < 5" |> parse_term |> assume_rule
// val it : thm = x + y < 5 |- x + y < 5

spec_rule ("a = 0" |> parse_term) excluded_middle_thm
// val it : thm = |- a = 0 \/ ~ (a = 0)

(**
Le dimostrazioni sono semplicemente espressioni F# composte con applicazioni di regole di inferenza ad ogni livello.
*)

deduct_antisym_rule
    (contr_rule ("~ true" |> parse_term) (assume_rule ("false" |> parse_term)))
    (eq_mp_rule (eqf_intro_rule (assume_rule ("~ true" |> parse_term))) truth_thm)
// val it : thm = |- ~ true <=> false

(**
il sistema supporta le seguenti teorie matematiche di base: logica predicativa, lambda calcolo, coppie ordinate e aritmetica dei numeri naturali.

Le teorie del sistema possono essere estese usando i comandi di teoria per dichiarare nuove costanti e costanti di tipo e per enunciare proposizioni a loro riguardo. Per esempio, il comando di definizione di costante introduce una nuova costante e restituisce un nuovo teorema, che afferma che il valore della costante è uguale a un'espressione data. Prende un termine di uguaglianza con la nuova costante come lato sinistro del'eguaglianza e il valore della costante come lato destro.
*)

"max_height = 7" |> parse_term |> new_const_definition
// [HZ] Declaring constant "max_height".
// [HZ] Adding definition for constant "max_height".
// val it : thm = |- max_height = 7


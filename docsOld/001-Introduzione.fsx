(**

Introduzione
===========

HOL Zero è un dimostratore di teoremi minimale nella logica HOL. NHOLZ è un porting di HOL Zero in F# che ha lo scopo di avere un dimostratore di teoremi HOL, cioè un programma che supporta dimostrazioni formali e lo sviluppo di teorie nella logica HOL (si veda più avanti), a disposizione in F# per lo studio a livello personale di sistemi di questo tipo. Ho scelto HOL Zero come base perché è un dimostratore di teoremi relativamente semplice che si concentra su buone funzionalità di base, robustezza architetturale, lo sviluppo della sintassi concreta, un prettyprinting completo e non ambiguo, e la leggibilità del codice sorgente e perché per le sue caratteristiche è risultato piuttosto semplice effettuarne il porting. 

Si tratta di un sistema non adatto allo sviluppo di dimostrazioni di grandi dimensioni. Esso, infatti, supporta soltanto uno stile di dimostrazione nella semplice deduzione naturale, e manca di funzionalità interattive ed automatiche  avanzate che altri sistemi HOL hanno.

1.1 Concetti Base
--------------

L'interazione utente con un sistema HOL avviene immettendo istruzioni a riga di comando in formato ASCII in una sessione interativa dell'interprete. Queste istruzioni sono di fatto espressioni nel linguaggio di programmazione che vengono valutate dall'interprete REPL una volta immesse. 

Coloro che hanno una più profonda conoscenza del linguaggio possono estenderne le funzionalità. Una modalità di estensione consiste nell'immettere definizioni in una sessione. Qualsiasi di queste estensioni sono sicure nel senso che non possono introdurre incoerenze logiche nel sistema. Questa sicurezza è garantita dal fatto che il sistema è implementato secondo quella che viene chiamata un'architettura nello ''stile LCF'' (si veda la Sessione 4.1.3).

**1.1.2 La logica HOL**

La logica HOL qui utilizzata è una logica predicativa tipizzata, classica, di ordine superiore, cioè una logica predicativa con un sistema di tipi, con la legge del terzo escluso come teorema, e con la possibilità di quantificare su funzioni. E' basata sul lambda calcolo tipizzato di Alonzo Church. Ha un sistema polimorfico di tipi relativamente semplice che non è dipendentemente tipizzato e non supporta la quantificazione su variabili di tipo. Si faccia riferimento al glossario per una spiegazione estesa di questi concetti.

La logica HOL fu sviluppata per la prima volta negli anni 1980 per un sistema prototipo chiamato Cambridge HOL, ed è ora supportata dalla famiglia di dimostratori di teoremi HOL che include HOL4, ProofPower HOL, HOL Light e Isabelle/HOL. Questi sistemi sono stati utilizzati come strumenti affidabili essenziali in una varietà di progetti industriali, che includono la verifica dello sviluppo di microcircuiti integrati per computer e software safety-critical. Essi sono anche preminenti nella formalizzazione della matematica, in particolare nell'innovativo progetto Flyspeck di Tom Hales per formalizzare la sua dimostrazione della congettura di Keplero.

**1.1.3 Common HOL**

Common HOL è uno standard per le funzionalità di base di un sistema HOL, che ha lo scopo di facilitare la portabilità del codice sorgente e delle dimostrazioni formali tra i membri della famiglia HOL. Esso consiste nelle seguenti componenti:

- la specifica di una API di funzionalità HOL di base, per permettere il porting del codice sorgente tra sistemi HOL compatibili;
- l'implementazione dell'API per vari sistemi HOL;
- la specifica di un formato di file di dimostrazione, per permettere il porting delle dimostrazioni formali tra sistemi HOL compatibili;
- l'implementazioni di oggetti per l'esportazione e l'importazione delle dimostrazioni tra vari sistemi HOL.

NHOLZ, in generale, supporta lo standard Common HOL avendolo ereditato da HOL Zero. Va, tuttavia, notato che non supporta le term e le type quotation.

1.2 Avviare una sessione
------------------------

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

1.3 Panoramica d'uso
--------------

Questa sezione fornisce una breve introduzione a semplici operazioni, incluso come immettere espressioni HOL e come eseguire una semplice dimostrazione. 

**1.3.1 Termini, Tipi e Teoremi**

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
1.3.2 Teoremi, Dimostrazioni ed Asserzioni
----------------------------------------

I teoremi HOL consistono di un insieme di termini di assunzione con valore booleano e di un termine conclusione con valore booleano, e sono riservati ad enunciati di cui si è stabilito che valgono (per dimostrazione o asserzione - si veda sotto). Il significato di tali enunciati è che la conclusione vale assumendo che valgano tutte le assunzioni. I teoremi sono mostrati usando un turnstile (`|-`) per separare tutte le assunzioni dalla conclusione. Il sistema di base contiene già oltre 100 teoremi pre-dimostrati, ognuno dei quali non ha assunzione. Questi sono elencati nella sezione [Teoremi](005-Teoremi.html).
*)

excluded_middle_thm
(*** include-fsi-output ***)

(**
Le regole di inferenza della logica HOL sono qui implementate come funzioni F# che prendono teoremi e/o termini e restituiscono teoremi. Un passo di dimostrazione è eseguito semplicemente valutando l'applicazione di una tale funzione. Dettagli sulle regole d'inferenza sono forniti nella sezione [Regole d'inferenza](003-Inference_Rules.html)
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
il sistema supporta le seguenti teorie matematiche di base: logica predicativa, lambda calcolo, coppie ordinate e aritmetica dei numeri naturali. Dettagli circa ogni teoria sono forniti nella sezione [Teorie](004-Teorie.html).

Le teorie del sistema possono essere estese usando i comandi di teoria per dichiarare nuove costanti e costanti di tipo e per enunciare proposizioni a loro riguardo. Per esempio, il comando di definizione di costante introduce una nuova costante e restituisce un nuovo teorema, che afferma che il valore della costante è uguale a un'espressione data. Prende un termine di uguaglianza con la nuova costante come lato sinistro del'eguaglianza e il valore della costante come lato destro. Dettagli su ciascun comendo di teoria sono forniti nella sezione [Teorie](004-Teorie.html).
*)

"max_height = 7" |> parse_term |> new_const_definition
// [HZ] Declaring constant "max_height".
// [HZ] Adding definition for constant "max_height".
// val it : thm = |- max_height = 7
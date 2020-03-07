(**

Introduzione
===========


Questo &egrave; il Manuale Utente di NHOLZ e fornisce una descrizione completa di come usare il sistema.

1.1 Concetti Base
--------------

**1.1.1 NHOLZ**

NHOLZ &egrave; un porting di HOL Zero in F#. HOL Zero un dimostratore di teoremi HOL, cio&egrave; un programma 
che supporta dimostrazioni formali e lo sviluppo di teorie nella logica HOL (si veda pi&ugrave; avanti). Si tratta 
di un dimostratore di teoremi relativamente semplice che si concentra su buone funzionalit&agrave; di base, 
robustezza architetturale, lo sviluppo della sintassi concreta, un prettyprinting completo e non ambiguo, e la 
leggibilit&agrave; del codice sorgente. Le stesse qualit&agrave; lo rendono adatto come esempio pedagogico per logici, 
programmatori e informatici che vogliano comprendere come funzionano i dimostratori di teoremi.

NHOLZ non &egrave; adatto allo sviluppo di dimostrazioni di grandi dimensioni. Esso, infatti, supporta soltanto uno 
stile di dimostrazione nella semplice deduzione naturale, e manca di funzionalit&agrave; interattive ed automatiche 
avanzate che altri sistemi HOL hanno.

L'interazione utente con HOL avviene immettendo istruzioni a riga di comando in formato ASCII in una sessione 
interativa F#. Queste istruzioni sono di fatto espressioni nel linguaggio di programmazione che vengono valutate 
dal interprete REPL una volta immesse. 

Coloro che hanno una pi&ugrave; profonda conoscenza di F# possono estenderne le funzionalit&agrave;.E' possibile 
estendere il programma immettendo definizioni F# in una sessione di NHOLZ (la sessione di NHOLZ non &egrave; 
nient'altro che una sessione interativa F# con il codice sorgente di NHOLZ incorporata). Qualsiasi di queste estensioni 
sono sicure nel senso che non possono introdurre incoerenze logiche nel sistema. Questa sicurezza &egrave; garantita 
dal fatto che NHOLZ &egrave; implementato secondo quella che viene chiamata un'architettura nello ''stile LCF'' 
(si veda la Sessione 4.1.3), che &egrave; usata anche in altri sistemi HOL. NHOLZ supporta lo standard Common HOL.

**1.1.2 La logica HOL**

La logica HOL &egrave; una logica predicativa tipizzata, classica, di ordine superiore, cio&egrave; una logica 
predicativa con un sistema di tipi, con la legge del terzo escluso come teorema, e con la possibilit&agrave; di 
quantificare su funzioni. E' basata sul lambda calcolo tipizzato di Alonzo Church. Ha un sistema polimorfico di 
tipi relativamente semplice che non &egrave; dipendentemente tipizzato e non supporta la quantificazione su 
variabili di tipo. Si faccia riferimento al glossario per una spiegazione estesa di questi concetti.

La logica HOL fu sviluppata per la prima volta negli anni 1980 per un sistema prototipo chiamato Cambridge HOL, ed 
&egrave; ora supportata dalla famiglia di dimostratori di teoremi HOL che include HOL4, ProofPower HOL, HOL Light 
e Isabelle/HOL. Questi sistemi sono stati utilizzati come strumenti affidabili essenziali in una variet&agrave; di 
progetti industriali, che includono la verifica dello sviluppo di microcircuiti integrati per computer e software 
safety-critical. Essi sono anche preminenti nella formalizzazione della matematica, in particolare nell'innovativo 
progetto Flyspeck di Tom Hales per formalizzare la sua dimostrazione della congettura di Keplero.

**1.1.3 Auditing di dimostrazione**

L'auditing delle dimostrazioni &egrave; il processo umano di determinare se uno script di dimostrazione che afferma 
di dimostrare un enunciato lo prova realmente. Questo dovrebbe essere fatto quando un'importante dimostrazione formale 
&egrave; stata completata, perch&eacute; ci sono varie insidie quando si usano dei dimostratori di teoremi, ognuna delle 
quali pu&ograve; concepibilmente rendere la pretesa dimostrazione formale completamente invalida. Questi variano da 
errori di base, come il fatto che lo script di dimostrazione non risulti in una dimostrazione formale di successo, o il 
fatto che lo script dimostri l'enunciato sbagliato, a problemi pi&ugrave; sottili come il fatto che le costanti che 
occorrono nell'enunciato dimostrato abbiano definizioni non corrette, che la teoria accumulata dal dimostratore di 
teoremi sia diventata incoerente, o il fatto che il dimostratore di teoremi stesso abbia degli errori nel suo disegno 
o nella implementazione.

L'auditing delle dimostrazioni indirizza questi problemi revisionando lo script di dimostrazione. Questo richiede come 
minimo il sistema originale per eseguire lo script, cos&igrave; che esso possa essere ri-eseguito attraverso quel 
sistema. L'auditor ha bisogno anche di eseguire controlli sull'enunciato dimostrato, le definizioni usate e la coerenza 
della teoria. Questi controlli sarebbero fatti normalmente usando il sistema originale, e l'auditor dovrebbe tener conto 
delle insidie in questo sistema ed assicurarsi in qualche modo che queste insidie non siano state sfruttate (in modo 
intenzionale o meno) dallo script di dimostrazione.

NHOLZ offre una soluzione pi&ugrave; efficace rispetto a quella di usare il sistema originale per eseguire questi 
controlli, agendo come un controllore della dimostrazione indipendente da usare per rieseguire la dimostrazione 
formale originaria (usando qualche oggetto di importazione della dimostrazione, per esempio si veda di seguito il 
paragrafo Common HOL) e per eseguire i controlli su di essa. Questo rimuove ogni preoccupazione legata a insidie 
relative alla consistenza nel sistema originale e la necessit&agrave; di esaminare lo script di dimostrazione. A 
causa delle sue credenziali di affidabilit&agrave;, non c'&egrave; alcuna necessit&agrave; da parte dell'auditor 
di indirizzare problemi legati alla consistenza nel controllore di dimostrazione. Cos&igrave; il processo di auditing 
della dimostrazione &egrave; semplificato e allo stesso tempo &egrave; significativamente ampliata la sicurezza che 
esso fornisce.

**1.1.4 Common HOL**

Common HOL &egrave; uno standard per le funzionalit&agrave; di base di un sistema HOL, che ha lo scopo di facilitare la portabilit&agrave; del codice sorgente 
e delle dimostrazioni formali tra i membri della famiglia HOL. Esso consiste nelle seguenti componenti:

- la specifica di una API di funzionalit&agrave; HOL di base, per permettere il porting del codice sorgente tra sistemi HOL compatibili;
- l'implementazione dell'API per vari sistemi HOL;
- la specifica di un formato di file di dimostrazione, per permettere il porting delle dimostrazioni formali tra sistemi HOL compatibili;
- l'implementazioni di oggetti per l'esportazione e l'importazione delle dimostrazioni tra vari sistemi HOL.

Tutte queste componenti, eccetto l'export di dimostrazione, sono liberamente disponibili sul sito Proof Technologies. I sistemi attualmente 
supportati sono NHOLZ, HOL Light e HOL90. L'export di dimostrazione &egrave; disponibile come servizio commerciale da parte di Proof Technologies, 
bench&eacute; varie dimostrazioni esportate siano liberamente disponibili sul sito. Si veda il file README di NHOLZ per il sito e i dettagli di 
contatto.

[Si noti che queste componenti non sono ancora disponibili sul sito web!!! Contattare Proof Technologies se si desidera averli.]

1.2 Avviare una sessione
------------------------

Una sessione di NHOLZ &egrave; avviata da uno script F#. Innanzitutto &egrave; necessario referenziare la dll 
e importare i relativi moduli:

*)

#I "../bin/netstandard2.0"
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

I primi pochi secondi di avvio di NHOLZ richiedono il build del sistema da zero. Alcune centinaia di righe di output 
scorrono velocemente sullo schermo. 

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

NHOLZ &egrave; quindi pronto per ricevere i comandi dall'utente.
Questi comandi sono di fatto espressioni F#.

1.3 Panoramica d'uso
--------------

Questa sezione fornisce una breve introduzione a semplici operazioni in NHOLZ, incluso come immettere espressioni 
HOL e come eseguire una semplice dimostrazione. Per informazioni pi&ugrave; approfondite circa l'uso di NHOLZ, 
il lettore dovrebbe procedere nei capitoli seguenti del manuale.

**1.3.1 Termini, Tipi e Teoremi**

Le espressioni nel linguaggio HOL sono chiamati termini HOL. I termini sono scritti utilizzando una stringa di caratteri 
ASCII a cui va applicata la funzione `parse_term`. Nel momento in cui si immette un termine in una sessione 
di NHOLZ questo viene controllato e ristampato a video.

La sintassi dei termini &egrave; semplice e intuitiva, e si va incontro a vari meccanismi sintattici. 
Per esempio, il seguente termine significa ''per tutti i numeri naturali `x`, `y` e `z`, se `x` &egrave; 
minore di `y` e `y` &egrave; minore di `z` allora `x` &egrave; minore di `z`'':

*)

@"!x y z. x < y /\ y < z ==> x < z" |> parse_term
//val it : term = `!x y z. x < y /\ y < z ==> x < z`

(**

Se si immette un termine mal formato si ricever&agrave; un messaggio di errore.

*)

"x =" |> parse_term

// > 
// HOL.Exn+HolErr: [HZ] SYNTAX ERROR: Unexpected end of quotation instead of RHS for infix "="
// ...

(**

Si noti che i messaggi specifici di NHOLZ, diversamente da quelli che derivano dall'interprete F#  
in generale, hanno il prefisso `[HZ]'. Questo vale per tutti i messaggi riportati da NHOLZ, inclusi 
messaggi di errore, warnings e feedback generici all'utente.

HOL &egrave; un linguaggio tipizzato, cos&igrave; ogni termine e sottotermine ha un tipo, e i termini 
devono essere costruiti in modo da avere un tipo corretto. Questo impedisce la costruzione di enunciati 
privi di significato come ''3 &egrave; uguale a vero''.
*)

"3 = true" |> parse_term
// > 
// HOL.Exn+HolErr: [HZ] TYPE ERROR: Function subterm domain type incompatible with argument subterm type

(**
I sottotermini nei term quotation possono essere annotati per indicare il loro tipo, facendo seguire al sottotermine 
il simbolo di i due punti (`:') e poi il suo tipo, il tutto chiuso tra parentesi. 
a video con annotazioni di tipo sufficienti almeno ad evitare qualsiasi ambiguit&agrave; circa il tipo di ogni 
sottotermine.
*)

"!(x:nat) (y:nat). x = y" |> parse_term
//val it : term = `!(x:nat) y. x = y`

(**
Il meccanismo di inferenza del tipo &egrave; usato per risolvere i tipi nei termini. Ad ogni termine inserito 
senza annotazioni di tipo sufficienti sono assegnate delle variabili di tipo numerate per tutti i tipi non 
determinabili.
*)

"!x y. x = y" |> parse_term
//val it : term = `!(x:'1) y. x = y`

(**
I tipi HOL possono essere scritti fuori dal contesto di un termine usando la funzone `parse_type`. 
*)

"nat#nat->bool" |> parse_type
//val it : hol_type = `:nat#nat->bool`

(**
1.3.2 Teoremi, Dimostrazioni ed Asserzioni
----------------------------------------

I teoremi HOL consistono di un insieme di termini di assunzione con valore booleano 
e di un termine conclusione con valore booleano, e sono riservati ad enunciati di cui  
si &egrave; stabilito che valgono (per dimostrazione o asserzione - si veda sotto). 
Il significato di tali enunciati &egrave; che la conclusione vale assumendo che 
valgano tutte le assunzioni. I teoremi sono mostrati usando un runstile (`|-`) per 
separare tutte le assunzioni dalla conclusione. Il sistema di base contiene gi&agrave; 
oltre 100 teoremi pre-dimostrati, ognuno dei quali non ha assunzione. Questi sono 
elencati nell'Appendice B2.

*)

excluded_middle_thm
//val it : thm = |- !p. p \/ ~ p

(**
Le regole di inferenza della logica HOL sono implementate in NHOLZ come funzioni F# che prendono 
teoremi e/o termini e restituiscono teoremi. Un passo di dimostrazione &egrave; eseguito semplicemente 
valutando l'applicazione di una tale funzione. Dettagli sulle regole d'inferenza sono forniti 
nell'Appendice A5
*)

"x + y < 5" |> parse_term |> assume_rule
//val it : thm = x + y < 5 |- x + y < 5

spec_rule ("a = 0" |> parse_term) excluded_middle_thm
//val it : thm = |- a = 0 \/ ~ (a = 0)

(**
Le dimostrazioni sono semplicemente espressioni ML composte con applicazioni di regole di inferenza ad ogni livello.
*)

deduct_antisym_rule
    (contr_rule ("~ true" |> parse_term) (assume_rule ("false" |> parse_term)))
    (eq_mp_rule (eqf_intro_rule (assume_rule ("~ true" |> parse_term))) truth_thm)
//val it : thm = |- ~ true <=> false

(**
il sistema di base supporta le seguenti teorie matematiche di base: logica predicativa, lambda calcolo, 
coppie ordinate e aritmetica dei numeri naturali. Dettagli circa ogni teoria sono forniti 
nell'Appendice B1

Le teorie del sistema possono essere estese usando i comandi di teoria per dichiarare nuove 
costanti e costanti di tipo e per enunciare proposizioni a loro riguardo. Per esempio, il 
comando di definizione di costante introduce una nuova costante e restituisce un nuovo 
teorema, che afferma che il valore della costante &egrave; uguale a un'espressione data. 
Prende un termine di uguaglianza con la nuova costante come lato sinistro del'eguaglianza e 
il valore della costante come lato destro. Dettagli su ciascun comendo di teoria sono forniti 
nell'Appendice A4.
*)

"max_height = 7" |> parse_term |> new_const_definition
//[HZ] Declaring constant "max_height".
//[HZ] Adding definition for constant "max_height".
//val it : thm = |- max_height = 7
# NHolZ

NHOLZ è il porting in F# di [HOL Zero](http://www.proof-technologies.com/holzero/): un dimostratore di teoremi nella logica HOL. Lo scopo è quello di avere un dimostratore di teoremi HOL, cioè un programma che supporta dimostrazioni formali e lo sviluppo di teorie nella logica HOL, a disposizione in F# per lo studio a livello personale di sistemi di questo tipo. Ho scelto HOL Zero come base perché, come dice il suo autore, "è un dimostratore di teoremi relativamente semplice che si concentra su buone funzionalità di base, robustezza architetturale, lo sviluppo della sintassi concreta, un prettyprinting completo e non ambiguo, e la leggibilità del codice sorgente" e perché per le sue caratteristiche è risultato piuttosto semplice effettuarne il porting. 

## Che cos'è un sistema HOL?

Un sistema HOL è un sistema informatico sviluppato per supportare la dimostrazione interattiva di teoremi nella logica di ordine superiore (da qui l'acronimo HOL per Higher Order Logic). A questo scopo, la logica formale è interfacciata da un linguaggio di programmazione di uso generale (originariamente l'ML, per meta-linguaggio, ma qui F#) in cui si possono denotare i termini e i teoremi della logica, esprimere ed applicare le strategie di dimostrazione, e sviluppare teorie logiche. 

L'idea base (derivata dall'approccio [LCF](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions)) è quella di utilizzare un *tipo di dati astratto* per i *teoremi* in modo tale, però, che 'istanze' di tale tipo siano costruibili solo a partire da un insieme di funzioni che implementano regole di inferenza logica e che tali regole siano nel loro insieme valide.

La logica di ordine superiore usata in HOL è una versione del calcolo dei predicati con i termini del lambda calcolo tipizzato (cioè la teoria semplice dei tipi). Questa fu originariamente sviluppata come una fondazione per la matematica da Church 1940<sup>[1](## 'A formulation of the simple theory of types. Journal of Symbolic Logic, 5:56–68, 1940.')</sup>.

Nello specifico la logica implementata in HOL Zero è "una logica predicativa tipizzata, classica, di ordine superiore, cioè una logica predicativa con un sistema di tipi, con la legge del terzo escluso come teorema, e con la possibilità di quantificare su funzioni."



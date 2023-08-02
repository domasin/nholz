(**

LINGUAGGIO HOL
=============

Il linguaggio HOL &egrave; un potente linguaggio formale in grado di descrivere la maggior parte 
della matematica. Questo capitolo spiega il liguaggio e la versione di sintassi concreta usata dal sistema.
Spiega inoltre varie operazioni che si possono eseguire sulle espressioni, e 
come configurare l'input e l'output

3.1 Sintassi lessicale
------------

Questa sezione spiega la sintassi lessicale usata sia per i tipi che i termini (si vedano rispettivamente 
le sezioni 3.2.2 e 3.2.3). Per una grammatica formale della sintassi lessicale si veda l'Appendice C.

**3.1.1 Token**

I tipi e i termini si dividono in una lista di token lessicali. I token identificatori sono usati 
per riferirsi esplitamente a entit&agrave; HOL (cio&egrave; variabili, costanti, variabili di tipo 
e costanti di tipo). I token parole riservate aiutano a dare una struttura sintattica. Qualsiasi 
tipo di spazio tra identificatori e/o token non viene a sua volta catturato in token.

Per esempio il seguente termine (Esempio 3.1):

`\x. y + foo x`


si divde in 7 token: `\`, `x`, `.`, `y`, `+`, `foo`, `x`. 

`x`, `y`, `foo` e la costante `+` costituiscono toke indentificatori, mentre 
`\` e `.` sono token di parole riservate.

HOL &egrave; case sensitive sia nei confronti di nomi di entit&agrave; che 
rispetto a parole riservate.

**3.1.2 Nomi regolari e irregolari**

Tutte le entit&agrave; HOL hanno almeno un attributo nome, che nel sistema corrente &egrave; una sequenza 
di caratteri ASCII. Non ci sono restrizioni sulla forma di questo nome - potenzialmente pu&ograve; coinvolgere 
qualsiasi combinazione di cifre, underscore, caratteri simbolici, spazi o persino caratteri non stampabili, 
cos&igrave; come caratteri alfanumerici.

Tuttavia, la forma di token identificatori che pu&ograve; essere usata per riferirisi a entit&agrave; HOL 
dipende dal fatto che il nome dell'entit&agrave; sia ''regolare'' o ''irregolare''. l'identificatore per 
un nome regolare pu&ograve; essere semplicemente il nome stesso (cos&igrave; come per tutte le entit&agrave; 
nell'esempio 3.1), mentre l'identificatore per un nome irregolare richiede una quotazione (si veda 
la Sezione 3.1.5).

Ci sono tre forme di nomi regolari:

1. Alfanumerici
    - iniziano con una lettera o con un `_`, seguiti da zero o pi&ugrave; lettere, cifre, 
        altri `_` e `'`.
2. Numerici
    - iniziano con una cifra, seguita da zero o pi&ugrave; cifre e `_`
    - non possono essere seguiti immediatamente da una lettera o da `'`
3. Simbolici
    - uno o pi&ugrave; dei seguenti caratteri: `! # & * + - . / ; < = > ? @ | ~ ^ [ ] \ { }`

Tutti gli altri nomi sono irregolari. Questi includono qualsiasi nome che contenga caratteri di spazio, 
punteggiatura, caratteri non stampabili o una miscela di caratteri alfanumerici e simbolici. Include anche 
la sequenza vuota di caratteri.

- Caratteri di spazio: space, tab, line-feed, form-feed, carriage-return
- Caratteri di punteggiatura: `( ) , :`
- Caratteri non stampabili: qualsiasi codice ASCII < 32 o > 126

**3.1.3 Parole Riservate**

Ci sono tre forme di toke di parola riservata:

1. Punteggiatura:
    - un singolo carattere di punteggiatura (si veda la Sezione 3.1.2)
2. Parola chiave:
    - un nome regolare non-numerico da questo insieme fisso di 8 token: `and else if in let then \ .`
3. Parentesi di enumerazione:
    - un nome regolare non-numerico per delimitare l'inizio o la fine di espressioni di enumerazione
    - l'utente pu&ograve; estendere l'insieme delle parentesi di enumerazione (si veda la Sezione 3.4.4)
    - nel sistema base non &egrave; definita alcuna parentesi di enumerazione 

Identificatori per entit&agrave; con nomi che vanno in conflitto con parole riservate richiedono il 
quoting (si veda la Sezione 3.1.5).

Si noti che il token lessicale `=` &egrave; un caso speciale nella sintasi lessicale di HOL.
Bench&egrave; sia normalmente un identificatore, e sia classificato come tale dalla 
sintassi lessicale, &egrave; di fatto una parola chiave quando occore come parte di una dichiarazione 
let (si veda la Sezione 3.4.2).

**Giustapposizione di token**

Le quotazioni devono essere scritte con parentesi e spaziature sufficienti da distinguere token 
alfanumerici/numerici adiacenti o token simbolici adiacenti (sia che questi token siano 
identificatori o parole riservate). Per esempio, in `\ ^ . ^ = 5` (dove `^` di fatto &egrave; una 
variabile), &egrave; inserita una spaziatura tra `\` e`^`, e tra `^` e `.`, che sono tutti token 
simbolici

**3.1.5 Quoting di identificatori**

Gli identificatori per entit&agrave; con nomi irregolari o nomi che vanno in conflitto con parole 
riservate devono essere delimitati in modo speciale. Questo implica aggiungere un carattere di doppio 
apice all'inizio e alla fine del nome, come in `"then" = "foo x"` (che significa la variabile con nome 
`"then"` &egrave; uguale alla variabile chiamata `"foo x"`). Questo meccanismo &egrave; chiamato 
''quoting di identificatore''.

Qualsiasi carattere `"` o `\` in un nome quotato deve essere preceduto da un carattere backslash di escape, 
come in `\\ \"` (per un carattere di backslash seguito da un carattere di spazio seguito da un carattere di 
doppio apice). Ogni carattere di backquote o non stampabilie in un nome quotato deve essere immesso con un 
backslash seguito dal codice ASCII decimale di 3 cifre (con degli zero iniziali per caratteri con codici 
ASCII minori di 100), come in `\007\127` per il carattere ASCII 7 seguito dal carattere ASCII 127. Questi 
codici ASCII di 3 cifre possono essere usati anche per i caratteri stampabili, come in `\111\107` (per 
`ok`), ma questo naturalmente non &egrave; richiesto.

Anche le variabili e le costanti con nomi numerici devono essere quotate (perch&eacute; i token numerici nei 
termini denotano numerali di numeri naturali - Si veda la Sezione 3.4.5). Questo non si applica alle 
variabili di tipo e alle costanti di tipo con nomi numerici.

Il quoting di nomi di entit&agrave; che non lo richiedono (cio&egrave; quelle regolari, o con nomi che non 
vanno in conflitto) &egrave; permesso, e denta lo stessa cosa del nome non quotato.

**3.1.6 Marcautre Speciali**

Gli identificatori possono avere un marcatire prefisso di un carattere per decrivere un'informazione 
extra. Il marcatore `$` indica che l'identificatore occore ''defixato'' (si veda la Sezione 3.5.8), come 
in `$=`. I marcatori `'` e `%` indicano rispettivamente che l'identificatore &egrave; per una variabile 
di tipo o per una variabile (si veda la Sezione 3.6.2), come in `'a` e `%x`.

Questi marcatori sono pare dello stesso token lessicale della parte principale dell'identificatore, e 
devono precederlo immediatamente, senza alcuno spazio infrapposto. Se l'identificatore usa il quoting 
(si veda la Sezione 3.1.5), allora i marcatori devono essere scritti fuori ed immediatamente 
prima dei doppi apici, come in `%"let"`.

Se un identificatore ha sia un marcatore di defizine e un marcatore di variabile o di variabile di tipo, 
allore il marcatore di defizine deve venire prima come in `$%=`.

*)

(1,2,3) |> fst

let _,_,z = 1,2,3
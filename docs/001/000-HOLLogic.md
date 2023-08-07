---
title: La logica HOL
category: HOL Logic
categoryindex: 1
index: 1
---

# La logica HOL

La logica supportata dai sistemi HOL è una variante della teoria dei tipi semplici di Church. 

La sintsassi di HOL contiene categorie sintattiche di tipi e termini i cui elementi sono
intesi denotare rispettivamente certi insiemi e elementi di insiemi. Di seguito sarà sviluppata questa interpretazione insiemisitica accanto alla descrizione della sintassi di del linguaggio, e più avanti, il sistema di dimostrazione implementato sarà mostrato essere valido per il ragionamento circa proprietà del modello insiemistico.

## Universo

Il modello insiemistico è dato in termini di un insieme di insiemi fisso $\cal U$, che sarà chiamato l'*universo* e che si assume avere le seguenti proprietà:

|---------------|-------------
| **Inhab**     | Ogni elemento di $\cal U$ è un insieme non vuoto.
| **Sub**       | Se $X\in{\cal U}$ e $\emptyset\not=Y\subseteq X$, allora $Y\in{\cal U}$  
| **Prod**      | Se $X\in{\cal U}$ e $Y\in{\cal U}$, allora $X \times Y\in{\cal U}$. L'insieme $X\times Y$ è il prodotto cartesiano, consistente di coppie ordinate $(x,y)$ con $x\in X$ e $y\in Y$, con l'usuale notazione insiemistica delle coppie ordinate, cioé $(x,y)=\{\{x\},\{x,y\}\}$.
| **Pow**       | Se $X\in{\cal U}$, allora anche l'insieme potenza $P(X)=\{Y:Y\subseteq X\}$ è un elemento di $\cal U$.
| **Infty**     | $\cal U$ contiene un distinto insieme infinito $\cal I$.
| **Choice**    | C'è un elemento distinto $ch\in\prod_{X\in{\cal U}}X$ (il prodotto cartesiano generalizzato). Gli elementi del prodotto $\prod_{X\in{\cal U}}X$ sono funzioni (dipendentemente tipizzate): così per tutti gli $X\in{\cal U}$, $X$ è non vuoto per *Inhab* e $ch(X)\in X$ testimonia questo<sup>[†](## 'Il prodotto cartesiano generalizzato  è definito come l'insieme di tutte le funzioni che mandano ciascun elemento X in U in un qualche elemento di X. Queste funzioni si possono, dunque, considerare come se scegliessero per ogni elemento X in U un elemento di X rappresentativo di tutto l'insieme X e per questo si parla di funzioni di scelta. Choice isola una di queste funzioni: ch.')</sup>.

Da queste assunzioni seguono, come conseguenze, anche le seguenti ulteriori proprietà che è utile esplicitare (e nominare per potervi fare riferimento velocemente):

|---------------|-------------
| **Fun**       | Se $X\in{\cal U}$ e $Y\in{\cal U}$, allora $X\rightarrow Y\in{\cal U}$<sup>[†](## 'Nella teoria degli insiemi le funzioni sono identificate dai loro grafi, che sono certi insiemi di coppie ordinate. Cosı̀ l’insieme X -> Y di tutte le funzioni da un insieme X a un insieme Y è un sottoinsieme di P(X × Y); ed è un insieme non vuoto quando Y non è vuoto. Cosı̀ Sub, Prod e Pow insieme implicano che U soddisfi la proprietà Fun.')</sup>. 
| **Unit**      | $\cal U$ contiene un distinto insieme di un solo elemento $1=\{0\}$<sup>[†](## 'Iterando Prod, si ottiene che il prodotto cartesiano di qualsiasi numero finito, diverso da zero, di insiemi in U è ancora in U. U contiene anche il prodotto cartesiano di nessun insieme, il che equivale a dire che contiene un insieme di un unico elemento (in virtù di Sub applicato a qualsiasi insieme in U e Infty garantisce che ce n’è uno); per precisione, Unit isola un particolare insieme di un solo elemento.')</sup>.
| **Bool**      | $\cal U$ contiene un distinto insieme di due elementi $2=\{0,1\}$<sup>[†](## 'Analogamente a Unit, a causa di Sub e Infty, U contiene insiemi di due elementi, uno dei quali viene isolato.')</sup>.

## Tipi

I tipi della logica HOL sono espressioni che denotano insiemi (nell’universo U). Nel seguito il simbolo $\sigma$, possibilmente decorato con sottoscritti o primi, è usato per variare su tipi arbitrari.

Ci sono quattro specie di tipi nella logica HOL. Questi possono essere descritti informalmente dalla seguente grammatica BNF, in cui $\alpha$ varia su variabili di tipo, $c$ varia su tipi atomici e $op$ varia su operatori di tipo.

$$\sigma\quad ::=\quad {\mathord{\mathop{\alpha}\limits_{variabili\ di\ tipo}}}
        \quad\mid\quad{\mathord{\mathop{c}\limits_{tipi\ atomici}}}
        \quad\mid\quad\underbrace{(\sigma_1, \ldots , \sigma_n){op}}_{tipi\ composti}
        \quad\mid\quad\underbrace{\sigma_1\rightarrow\sigma_2}_{tipi\ funzione}$$

* **Variabili di tipo**: stanno per insiemi arbitrari nell'universo.

* **Tipi atomici**: denotano insiemi fissati nell'universo. Ogni teoria determina una particolare collezione di tipi atomici. Per esempio, i tipi atomici standard $bool$ (vedi `cref:P:HOL.CoreThry.bool_ty`) e $ind$ (`cref:P:HOL.Ind.ind_ty`) denotano, rispettivamente, l'insieme distinto di $2$ elementi e l'insieme distinto infinito $\cal I$.

* **Tipi composti**: hanno la forma $(\sigma_1, \ldots, \sigma_n)op$, dove $\sigma_1, \ldots, \sigma_n$ sono tipi argomento e $op$ è un *operatore di tipo* di arietà $n$. Gli operatori di tipo denotano operazioni per costruire insiemi. Il tipo $(\sigma_1, \ldots, \sigma_n)op$ denota l'insieme che risulta dall'applicare l'operazione denotata da $op$ agli insiemi denotati da $\sigma_1, \ldots, \sigma_n$. Per esempio, se indichiamo con $prod$ l'operatore di tipo di arietà $2$ che denota l'operazione di prodotto cartesiano, $(\sigma_1, \sigma_2)prod$ indicherà il prodotto cartesiano degli insiemi denotati rispettivamente da $\sigma_1$ e $\sigma_2$ o, equivalentemente, l'insieme di coppie ordinate di elementi di $\sigma_1$ e $\sigma_2$. $(\sigma_1, \sigma_2)prod$ è anche scritto $\sigma_1 \times \sigma_2$. Si noti che $prod$ qui è implementato con il simbolo '#' (`cref:P:HOL.Pair.prod_def`).

* **Tipi funzione**: Se $\sigma_1$ e $\sigma_2$ sono tipi, allora $\sigma_1 \rightarrow \sigma_2$ è il tipo funzione con *dominio* $\sigma_1$ e rango $\sigma_2$. Esso denota l'insieme di tutte le funzioni (totali) dall'insieme denotato dal suo dominio all'insieme denotato dal suo rango. Si not che sintatticamente $\rightarrow$ è semplicmente un distinto operatore di tipo di arietà $2$ scritto con notazione infissa. E' isolato nelladefinizione dei tipi HOL perché denoterà sempre la stessa operazione in qualsiasi modello di una teoria HOL (si veda [CoreThry](https://github.com/domasin/nholz/blob/master/src/CoreThry.fs#L41)) - contrariamente agli altri operatori di tipo che possono essere interpretati in modo differente in modelli differenti. (Si veda più avanti TODO indicare precisamente dove).

Risulta conveniente identificare i tipi atomici con tipi composti costruiti con operatori di tipo $0$-ari. Per esempio, il tipo atomico $bool$ dei valori di verità può essere considerato come un’abbreviazione per $()bool$. Questa identificazione sarà fatta nei dettagli tecnici che seguono, ma nella presentazione informale i tipi atomici continueranno ad essere distinti dai tipi composti, e $()c$ sarà scritto come $c$.
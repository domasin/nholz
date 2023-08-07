# La logica HOL

La logica supportata dai sistemi HOL è una variante della teoria dei tipi semplici di Church. 

La sintsassi di HOL contiene categorie sintattiche di tipi e termini i cui elementi sono
intesi denotare rispettivamente certi insiemi e elementi di insiemi. Questa interpretazione insiemisitica sarà sviluppata accanto alla descrizione della sintassi di HOL, e più avanti, il sistema di dimostrazione implementato sarà mostrato essere valido per il ragionamento circa proprietà del modello insiemistico.

## Universo

Il modello insiemistico è dato in termini di un insieme di insiemi fisso $\cal U$, che sarà chiamato l'*universo* e che si assume avere le seguenti proprietà:

|---------------|-------------
| **Inhab**     | Ogni elemento di $\cal U$ è un insieme non vuoto.
| **Sub**       | Se $X\in{\cal U}$ e $\emptyset\not=Y\subseteq X$, allora $Y\in{\cal U}$  
| **Prod**      | Se $X\in{\cal U}$ e $Y\in{\cal U}$, allora $X \times Y\in{\cal U}$. L'insieme $X\times Y$ è il prodotto cartesiano, consistente di coppie ordinate $(x,y)$ con $x\in X$ e $y\in Y$, con l'usuale notazione insiemistica delle coppie ordinate, cioé $(x,y)=\{\{x\},\{x,y\}\}$.
| **Pow**       | Se $X\in{\cal U}$, allora anche l'insieme potenza $P(X)=\{Y:Y\subseteq X\}$ è un elemento di $\cal U$.
| **Infty**     | $\cal U$ contiene un distinto insieme infinito $\cal I$.
| **Choice**    | C'è un elemento distinto $ch\in\prod_{X\in{\cal U}}X$ (il prodotto cartesiano generalizzato). Gli elementi del prodotto $\prod_{X\in{\cal U}}X$ sono funzioni (dipendentemente tipizzate): così per tutti gli $X\in{\cal U}$, $X$ è non vuoto per *Inhab* e $ch(X)\in X$ testimonia questo<sup>[2](## 'Il prodotto cartesiano generalizzato  è definito come l'insieme di tutte le funzioni che mandano ciascun elemento X in U in un qualche elemento di X. Queste funzioni si possono, dunque, considerare come se scegliessero per ogni elemento X in U un elemento di X rappresentativo di tutto l'insieme X e per questo si parla di funzioni di scelta. Choice isola una di queste funzioni: ch.')</sup>.

Da queste assunzioni seguono, come conseguenze, anche le seguenti ulteriori proprietà che è utile esplicitare (e nominare per potervi fare riferimento velocemente):

|---------------|-------------
| **Fun**       | Se $X\in{\cal U}$ e $Y\in{\cal U}$, allora $X\rightarrow Y\in{\cal U}$<sup>[3](## 'Nella teoria degli insiemi le funzioni sono identificate dai loro grafi, che sono certi insiemi di coppie ordinate. Cosı̀ l’insieme X -> Y di tutte le funzioni da un insieme X a un insieme Y è un sottoinsieme di P(X × Y); ed è un insieme non vuoto quando Y non è vuoto. Cosı̀ Sub, Prod e Pow insieme implicano che U soddisfi la proprietà Fun.')</sup>. 
| **Unit**      | $\cal U$ contiene un distinto insieme di un solo elemento $1=\{0\}$<sup>[4](## 'Iterando Prod, si ottiene che il prodotto cartesiano di qualsiasi numero finito, diverso da zero, di insiemi in U è ancora in U. U contiene anche il prodotto cartesiano di nessun insieme, il che equivale a dire che contiene un insieme di un unico elemento (in virtù di Sub applicato a qualsiasi insieme in U e Infty garantisce che ce n’è uno); per precisione, Unit isola un particolare insieme di un solo elemento.')</sup>.
| **Bool**      | $\cal U$ contiene un distinto insieme di due elementi $2=\{0,1\}$<sup>[5](## 'Analogamente a Unit, a causa di Sub e Infty, U contiene insiemi di due elementi, uno dei quali viene isolato.')</sup>.

## Tipi

I tipi della logica HOL sono espressioni che denotano insiemi (nell’universo U). Seguendo la tradizione,$\sigma$, possibilmente decorato con sottoscritti o primi, è usato per variare su tipi arbitrari.

Ci sono quattro specie di tipi nella logica HOL. Questi possono essere descritti informalmente dalla seguente grammatica BNF, in cui $\alpha$ varia su variabili di tipo, $c$ varia su tipi atomici e $op$ varia su operatori di tipo.

$$\sigma\quad ::=\quad {\mathord{\mathop{\alpha}\limits_{variabili\ di\ tipo}}}
        \quad\mid\quad{\mathord{\mathop{c}\limits_{tipi\ atomici}}}
        \quad\mid\quad\underbrace{(\sigma_1, \ldots , \sigma_n){op}}_{tipi\ composti}
        \quad\mid\quad\underbrace{\sigma_1\rightarrow\sigma_2}_{tipi\ funzione}$$
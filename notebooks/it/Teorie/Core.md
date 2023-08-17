# Teoria Core

## Costanti di tipo

| nome|sintassi|fixity
| :--- | :--- | :--- |
| bool            |`:bool`                         |Nonfix
| ->              |`:'1->'2`                       |Infix (5, RightAssoc)

 ## Costanti

| nome|sintassi|fixity
| :--- | :--- | :--- |
| true             |`:bool`                         |Nonfix
| ==>              |`:bool->bool->bool`             |Infix (10, RightAssoc)
| /\               |`:bool->bool->bool`             |Infix (20, RightAssoc)
| =                |`:'a->'a->bool`                 |Infix (30, NonAssoc)
| @                |`:('a->bool)->'a`               |Binder
| !                |`:('a->bool)->bool`             |Binder
| ?                |`:('a->bool)->bool`             |Binder
| ONE_ONE          |`:('a->'b)->bool`               |Nonfix
| TYPE_DEFINITION  |`:('a->bool)->('b->'a)->bool`   |Nonfix

## Costanti Alias

L'unico alias supportato è <=>, per un'istanza di '='.

| nome|sintassi|fixity
| :--- | :--- | :--- |
| <=>              |`:bool->bool->bool`             |Infix (5, NonAssoc)

## Definizioni

### true_def
      |- true <=> (\(p:bool). p) = (\p. p)

### conj_def
      |- $/\ = (\p1 p2. !p. (p1 ==> (p2 ==> p)) ==> p)

### forall_def
      |- $! = (\(P:'a->bool). P = (\x. true))

### exists_def
      |- $? = (\(P:'a->bool). P ($@ P))

### one_one_def
      |- ONE_ONE = (\(f:'a->'b). !x1 x2. f x1 = f x2 ==> x1 = x2)

### type_definition_def
      |- TYPE_DEFINITION =
            (\P (rep:'b->'a). ONE_ONE rep /\ (!x. P x <=> (?y. x = rep y)))

## Assiomi

### eta_ax
      |- !(f:'a->'b). (\x. f x) = f

### imp_antisym_ax
      |- !p1 p2. (p1 ==> p2) ==> ((p2 ==> p1) ==> (p1 <=> p2))

### select_ax
      |- !(P:'a->bool) x. P x ==> P ($@ P)

## Teoremi

### [fun_eq_thm](./Teoremi/Core/fun_eq_thm.ipynb)
      |- !(f:'a->'b) g. f = g <=> (!x. f x = g x)
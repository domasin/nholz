# Logica dei predicati

## Costanti

| nome|sintassi|fixity
| :--- | :--- | :--- |
| false            |`:bool`                         |Nonfix
| ~                |`:bool->bool`                   |Prefix
| \\/               |`:bool->bool->bool`             |Infix (15, RightAssoc)
| ?!               |`:('a->bool)->bool`             |Binder
| LET              |`:('a->'b)->'a->'b`             |Nonfix *
| ONTO             |`:('a->'b)->bool`               |Nonfix
| COND             |`:bool->'a->'a->'a`             |Nonfix *

## Definizioni

### false_def
      |- false <=> (!p. p)

### not_def
      |- $~ = (\p. p ==> false)

### disj_def
      |- $\/ = (\p1 p2. !p. (p1 ==> p) ==> (p2 ==> p) ==> p)

### uexists_def
      |- $?! = (\(P:'a->bool). ?x. P x /\ (!y. P y ==> y = x))

### let_def
      |- LET = (\(f:'a->'b) x. f x)

### onto_def
      |- ONTO = (\(f:'a->'b). !y. ?x. y = f x)

### cond_def
      |- COND =
           (\p (t1:'a) t2.
               @x. ((p <=> true) ==> x = t1) /\ ((p <=> false) ==> x = t2))

## Teoremi

### [bool_cases_thm](./Teoremi/Predicati/bool_cases_thm.ipynb)
      |- !p. (p <=> true) \/ (p <=> false)
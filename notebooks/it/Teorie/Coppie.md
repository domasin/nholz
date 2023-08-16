# Coppie ordinate

## Costanti di tipo

| nome|sintassi|fixity
| :--- | :--- | :--- |
| #            |`:'1#'2`                         |Infix (10, RightAssoc)

## Costanti

| nome|sintassi|fixity
| :--- | :--- | :--- |
| MkPairRep        |`:'a->'b->'a->'b->bool`         | Nonfix
| IsPairRep        |`:('a->'b->bool)->bool`         | Nonfix
| PairAbs          |`:('a->'b->bool)->'a#'b`        | Nonfix
| PairRep          |`:'a#'b->'a->'b->bool`          | Nonfix
| PAIR             |`:'a->'b->'a#'b`                | Nonfix *
| FST              |`:'a#'b->'a`                    | Nonfix
| SND              |`:'a#'b->'b`                    | Nonfix

## Definizioni di tipo

### prod_def

      |- ?(f:'a#'b->'a->'b->bool). TYPE_DEFINITION IsPairRep f

## Definizioni

TYPE DEFINITIONS

### prod_def
      |- ?(f:'a#'b->'a->'b->bool). TYPE_DEFINITION IsPairRep f

DEFINITIONS

### mk_pair_rep_def
      |- MkPairRep = (\(x:'a) (y:'b) a b. a = x /\ b = y)

### is_pair_rep_def
      |- IsPairRep = (\(r:'a->'b->bool). ?a b. r = MkPairRep a b)

### prod_def
      |- ?(f:'a#'b->'a->'b->bool). TYPE_DEFINITION IsPairRep f

### prod_bij_def1
      |- !(a:'a#'b). PairAbs (PairRep a) = a

### prod_bij_def2
      |- !(r:'a->'b->bool). IsPairRep r <=> PairRep (PairAbs r) = r

### pair_def
      |- PAIR = (\(x:'a) (y:'b). PairAbs (MkPairRep x y))

### fst_def
      |- FST = (\(p:'a#'b). @x. ?y. p = (x,y))

### snd_def
      |- SND = (\(p:'a#'b). @y. ?x. p = (x,y))
      
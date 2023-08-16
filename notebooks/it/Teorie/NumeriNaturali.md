# Numeri Naturali

## Costanti di tipo

| nome |sintassi | fixity
| :--- | :---    | :--- 
| nat  |`:nat`   | Nonfix

## Costanti

| nome     |sintassi          | fixity
| :---     | :---             | :--- 
| IsNatRep | `:ind->bool`     | Nonfix
| NatAbs   | `:ind->nat`      | Nonfix
| NatRep   | `:nat->ind`      | Nonfix
| ZERO     | `:nat`           | Nonfix
| SUC      | `:nat->nat`      | Nonfix
| PRE      | `:nat->nat`      | Nonfix
| +        | `:nat->nat->nat` | Infix (50, LeftAssoc)
| -        | `:nat->nat->nat` | Infix (50, LeftAssoc)
| *        | `:nat->nat->nat` | Infix (55, LeftAssoc)
| EXP      | `:nat->nat->nat` | Infix (60, LeftAssoc)
| EVEN     | `:nat->bool`     | Nonfix
| ODD      | `:nat->bool`     | Nonfix
| <        | `:nat->nat->bool`| Infix (40, NonAssoc)
| <=       | `:nat->nat->bool`| Infix (40, NonAssoc)
| >        | `:nat->nat->bool`| Infix (40, NonAssoc)
| >=       | `:nat->nat->bool`| Infix (40, NonAssoc)
| BIT0     | `:nat->nat`      | Nonfix
| BIT1     | `:nat->nat`      | Nonfix
| NUMERAL  | `:nat->nat`      | Nonfix

## Definizioni di tipo

### nat_def
    |- ?(f:nat->ind). TYPE_DEFINITION IsNatRep f

## Definizioni

### is_nat_rep_def
    |- !i. IsNatRep i <=> (!P. P IND_ZERO /\ (!j. P j ==> P (IND_SUC j)) ==> P i)

### nat_bij_def1
    |- !a. NatAbs (NatRep a) = a

### nat_bij_def2
    |- !r. IsNatRep r <=> NatRep (NatAbs r) = r

### zero_def
    |- ZERO = NatAbs IND_ZERO

### suc_def
    |- !n. SUC n = NatAbs (IND_SUC (NatRep n))

### pre_def
    |- PRE 0 = 0 /\ (!n. PRE (SUC n) = n)

### add_def
    |- (!n. 0 + n = n) /\ (!m n. SUC m + n = SUC (m + n))

### sub_def
    |- (!n. n - 0 = n) /\ (!m n. m - SUC n = PRE (m - n))

### mult_def
    |- (!n. 0 * n = 0) /\ (!m n. SUC m * n = n + m * n)

### exp_def
    |- (!n. n EXP 0 = 1) /\ (!m n. m EXP SUC n = m * m EXP n)

### even_def
    |- (EVEN 0 <=> true) /\ (!n. EVEN (SUC n) <=> ~ EVEN n)

### odd_def
    |- !n. ODD n <=> ~ EVEN n

### lt_def
    |- (!m. m < 0 <=> false) /\ (!m n. m < SUC n <=> m = n \/ m < n)

### le_def
    |- !m n. m <= n <=> m < n \/ m = n

### gt_def
    |- !m n. m > n <=> n < m

### ge_def
    |- !m n. m >= n <=> n <= m

### bit0_def
    |- (BIT0 ZERO = ZERO) /\ (!n. BIT0 (SUC n) = SUC (SUC (BIT0 n)))

### bit1_def
    |- !n. BIT1 n = SUC (BIT0 n)

### numeral_def
    |- !n. NUMERAL n = n
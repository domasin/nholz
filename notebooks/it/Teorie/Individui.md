# Individui

## Costanti di tipo

| nome|sintassi|fixity
| :--- | :--- | :--- |
| ind  |`:ind`| Nonfix

## Costanti

| nome|sintassi|fixity
| :--- | :--- | :--- |
| IND_ZERO  |       `:ind`            |              Nonfix
| IND_SUC   |       `:ind->ind`       |              Nonfix

## Definizioni

### ind_suc_zero_spec
    |- ONE_ONE IND_SUC /\ (!i. ~ (IND_SUC i = IND_ZERO))

## Assiomi

### infinity_ax
    |- ?(f:ind->ind). ONE_ONE f /\ ~ ONTO f


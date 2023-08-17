# fun\_eq\_thm

## Enunciato

$\vdash \forall f_{\alpha \rightarrow \beta}\ g.\ f = g \Leftrightarrow (\forall x.\ f\ x = g\ x)$

## Dimostrazione

$
{\dfrac
        {[f:\alpha\ \rightarrow\ \beta;g:\alpha\ \rightarrow\ \beta]
        \qquad
        {\dfrac
                {{\dfrac
                        {{\dfrac
                                {{\dfrac
                                        {\lambda\ x.\ (f:\alpha\ \rightarrow\ \beta)\ x}
                                        {\vdash\ (\lambda\ x.\ (f:\alpha\ \rightarrow\ \beta)\ x)\ =\ f}
                                        { eta\_conv}}}
                                {\vdash\ (f:\alpha\ \rightarrow\ \beta)\ =\ (\lambda\ x.\ f\ x)}
                                { sym\_rule}}
                        \qquad
                        {\dfrac
                                {x:\alpha
                                \qquad
                                {\dfrac
                                        {x:\alpha
                                        \qquad
                                        {\dfrac
                                                {\forall\ x.\ f\ x\ =\ (g:\alpha\ \rightarrow\ \beta)\ x}
                                                {\forall\ x.\ f\ x\ =\ g\ x\ \vdash\ \forall\ x.\ f\ x\ =\ (g:\alpha\ \rightarrow\ \beta)\ x}
                                                { assume\_rule}}}
                                        {\forall\ x.\ f\ x\ =\ g\ x\ \vdash\ f\ x\ =\ (g:\alpha\ \rightarrow\ \beta)\ x}
                                        { spec\_rule}}}
                                {\forall\ x.\ f\ x\ =\ g\ x\ \vdash\ (\lambda\ x.\ f\ x)\ =\ (\lambda\ x.\ (g:\alpha\ \rightarrow\ \beta)\ x)}
                                { mk\_abs\_rule}}
                        \qquad
                        {\dfrac
                                {\lambda\ x.\ (g:\alpha\ \rightarrow\ \beta)\ x}
                                {\vdash\ (\lambda\ x.\ (g:\alpha\ \rightarrow\ \beta)\ x)\ =\ g}
                                { eta\_conv}}}
                        {\forall\ x.\ f\ x\ =\ g\ x\ \vdash\ f\ =\ (g:\alpha\ \rightarrow\ \beta)}
                        { list\_trans\_rule}}
                \qquad
                {\dfrac
                        {x:\alpha
                        \qquad
                        {\dfrac
                                {{\dfrac
                                        {f\ =\ (g:\alpha\ \rightarrow\ \beta)}
                                        {f\ =\ g\ \vdash\ f\ =\ (g:\alpha\ \rightarrow\ \beta)}
                                        { assume\_rule}}
                                \qquad
                                x:\alpha}
                                {f\ =\ g\ \vdash\ f\ x\ =\ (g:\alpha\ \rightarrow\ \beta)\ x}
                                { mk\_comb1\_rule}}}
                        {f\ =\ g\ \vdash\ \forall\ x.\ f\ x\ =\ (g:\alpha\ \rightarrow\ \beta)\ x}
                        { gen\_rule}}}
                {\vdash\ f\ =\ (g:\alpha\ \rightarrow\ \beta)\ \Leftrightarrow\ (\forall\ x.\ f\ x\ =\ g\ x)}
                { deduct\_antisym\_rule}}}
        {\vdash\ \forall\ (f:\alpha\ \rightarrow\ \beta)\ g.\ f\ =\ g\ \Leftrightarrow\ (\forall\ x.\ f\ x\ =\ g\ x)}
        { list\_gen\_rule}}
$
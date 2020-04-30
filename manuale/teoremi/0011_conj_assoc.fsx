(**
Propriet&agrave; associativa della congiuzione

$\forall p\ q.\ p \wedge (q \wedge r) \Leftrightarrow (p \wedge q) \wedge r$
*)

(***hide***)
#load "../avvio.fsx"
open HOL
CoreThry.load
Equal.load
Bool.load
(***unhide***)

conj_assoc_thm
//   |- !p q r. p /\ (q /\ r) <=> (p /\ q) /\ r

([],"!p q r. p /\ (q /\ r) <=> (p /\ q) /\ r")
|> start_proof
|> list_gen_rule_bk
|> deduct_antisym_rule_bk [] []
|> conj_rule_bk [0] [0]
|> conjunct1_rule_bk "q:bool"
|> conjunct1_rule_bk "r:bool"
|> assume_rule_bk
|> conj_rule_bk [0] [0]
|> conjunct2_rule_bk "p:bool"
|> conjunct1_rule_bk "r:bool"
|> assume_rule_bk
|> conjunct2_rule_bk @"p /\ q"
|> assume_rule_bk
|> conj_rule_bk [0] [0]
|> conj_rule_bk [0] [0]
|> conjunct1_rule_bk @"q /\ r"
|> assume_rule_bk
|> conjunct1_rule_bk @"r:bool"
|> conjunct2_rule_bk @"p:bool"
|> assume_rule_bk
|> conjunct2_rule_bk @"q:bool"
|> conjunct2_rule_bk @"p:bool"
|> assume_rule_bk

|> view

(**
$
\small{ 	\color{green}{\dfrac
	{[p:bool;q:bool;r:bool]
	\qquad
	\color{green}{\dfrac
		{\color{green}{\dfrac
			{\color{green}{\dfrac
				{\color{green}{\dfrac
					{\color{green}{\dfrac
						{(p\ \wedge\ q)\ \wedge\ r}
						{(p\ \wedge\ q)\ \wedge\ r\ \vdash\ (p\ \wedge\ q)\ \wedge\ r}
						\textsf{ assume_rule}}}
					{(p\ \wedge\ q)\ \wedge\ r\ \vdash\ p\ \wedge\ q}
					\textsf{ conjunct1_rule}}}
				{(p\ \wedge\ q)\ \wedge\ r\ \vdash\ p}
				\textsf{ conjunct1_rule}}
			\qquad
			\color{green}{\dfrac
				{\color{green}{\dfrac
					{\color{green}{\dfrac
						{\color{green}{\dfrac
							{(p\ \wedge\ q)\ \wedge\ r}
							{(p\ \wedge\ q)\ \wedge\ r\ \vdash\ (p\ \wedge\ q)\ \wedge\ r}
							\textsf{ assume_rule}}}
						{(p\ \wedge\ q)\ \wedge\ r\ \vdash\ p\ \wedge\ q}
						\textsf{ conjunct1_rule}}}
					{(p\ \wedge\ q)\ \wedge\ r\ \vdash\ q}
					\textsf{ conjunct2_rule}}
				\qquad
				\color{green}{\dfrac
					{\color{green}{\dfrac
						{(p\ \wedge\ q)\ \wedge\ r}
						{(p\ \wedge\ q)\ \wedge\ r\ \vdash\ (p\ \wedge\ q)\ \wedge\ r}
						\textsf{ assume_rule}}}
					{(p\ \wedge\ q)\ \wedge\ r\ \vdash\ r}
					\textsf{ conjunct2_rule}}}
				{(p\ \wedge\ q)\ \wedge\ r\ \vdash\ q\ \wedge\ r}
				\textsf{ conj_rule}}}
			{(p\ \wedge\ q)\ \wedge\ r\ \vdash\ p\ \wedge\ q\ \wedge\ r}
			\textsf{ conj_rule}}
		\qquad
		\color{green}{\dfrac
			{\color{green}{\dfrac
				{\color{green}{\dfrac
					{\color{green}{\dfrac
						{p\ \wedge\ q\ \wedge\ r}
						{p\ \wedge\ q\ \wedge\ r\ \vdash\ p\ \wedge\ q\ \wedge\ r}
						\textsf{ assume_rule}}}
					{p\ \wedge\ q\ \wedge\ r\ \vdash\ p}
					\textsf{ conjunct1_rule}}
				\qquad
				\color{green}{\dfrac
					{\color{green}{\dfrac
						{\color{green}{\dfrac
							{p\ \wedge\ q\ \wedge\ r}
							{p\ \wedge\ q\ \wedge\ r\ \vdash\ p\ \wedge\ q\ \wedge\ r}
							\textsf{ assume_rule}}}
						{p\ \wedge\ q\ \wedge\ r\ \vdash\ q\ \wedge\ r}
						\textsf{ conjunct2_rule}}}
					{p\ \wedge\ q\ \wedge\ r\ \vdash\ q}
					\textsf{ conjunct1_rule}}}
				{p\ \wedge\ q\ \wedge\ r\ \vdash\ p\ \wedge\ q}
				\textsf{ conj_rule}}
			\qquad
			\color{green}{\dfrac
				{\color{green}{\dfrac
					{\color{green}{\dfrac
						{p\ \wedge\ q\ \wedge\ r}
						{p\ \wedge\ q\ \wedge\ r\ \vdash\ p\ \wedge\ q\ \wedge\ r}
						\textsf{ assume_rule}}}
					{p\ \wedge\ q\ \wedge\ r\ \vdash\ q\ \wedge\ r}
					\textsf{ conjunct2_rule}}}
				{p\ \wedge\ q\ \wedge\ r\ \vdash\ r}
				\textsf{ conjunct2_rule}}}
			{p\ \wedge\ q\ \wedge\ r\ \vdash\ (p\ \wedge\ q)\ \wedge\ r}
			\textsf{ conj_rule}}}
		{\vdash\ p\ \wedge\ q\ \wedge\ r\ \Leftrightarrow\ (p\ \wedge\ q)\ \wedge\ r}
		\textsf{ deduct_antisym_rule}}}
	{\vdash\ \forall\ p\ q\ r.\ p\ \wedge\ q\ \wedge\ r\ \Leftrightarrow\ (p\ \wedge\ q)\ \wedge\ r}
	\textsf{ list_gen_rule}} }
$
*)

let th1 = assume_rule_fd (parse_term(@"p /\ (q /\ r)")) in
let th2 = assume_rule_fd (parse_term(@"(p /\ q) /\ r")) in
list_gen_rule_fd [p;q;r]
  (deduct_antisym_rule_fd
    (* (p /\ q) /\ r |- p /\ (q /\ r)           *)
    (conj_rule_fd
      (conjunct1_rule_fd (conjunct1_rule_fd th2))
      (conj_rule_fd
        (conjunct2_rule_fd (conjunct1_rule_fd th2))
        (conjunct2_rule_fd th2) ))
    (* (p /\ q) /\ r |- (p /\ q) /\ r           *)
    (conj_rule_fd
      (conj_rule_fd
        (conjunct1_rule_fd th1)
        (conjunct1_rule_fd (conjunct2_rule_fd th1)) )
      (conjunct2_rule_fd (conjunct2_rule_fd th1)) ))
|> zipper
|> view
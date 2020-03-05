(* ========================================================================== *)
(* EXCEPTIONS (HOL Zero)                                                      *)
(* - Definitions of HOL Zero's specially supported exceptions                 *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2013                            *)
(* ========================================================================== *)

(* ========================================================================== *)
(* F# Porting                                                                 *)
(*                                                                            *)
(* by Domenico Masini 2013                                                    *)
(* http://github.com/domasin/nholz                                        *)
(* ========================================================================== *)

/// Questo modulo definisce tre nuove eccezioni di uso generale, insieme a una 
/// stampa di queste eccezioni.
[<AutoOpen>]      
module HOL.Exn

//* HolFail exception *//

/// <summary>
/// Questa eccezione è per errori che possono raggiungere alla fine il top level, 
/// ma che possono anche essere trappate chiamando delle funzioni. E' l'eccezione
/// classica per casi di errore nelle funzioni di HOL Zero.<para> </para>
/// 
/// Consiste del nome della funzione che fallisce e di un messaggio che descrive  
/// l'errore con qualche dettaglio. Di sotto sono definite varie funzioni per 
/// sollevare e trappare gli HolFails
/// </summary>
exception HolFail of (string * string)
    with
        override this.Message = 
            match this.Data0 with
            | (func,msg) -> "[HZ] FAIL: " + func + " - " + msg

/// Solleva un'eccezione HolFail
let hol_fail (func,msg) = raise (HolFail (func,msg))

//* HolErr exception *//

/// <summary>
/// Questa eccezione è per errori di corto-circuito che si ritirano direttamente al 
/// top level, evitando qualsiasi gestione per l'eccezioni di tipo HolFail.<para> </para> 
/// 
/// Essa consiste di una stringa (per convenzione in maiuscolo) che classifica l'eccezione i  
/// in modo generico, e di un messaggio che descrive l'eccezione in qualche dettaglio.
/// </summary>     
exception HolErr of (string * string)
    with
        override this.Message = 
            match this.Data0 with
            | (err,msg) -> "[HZ] " + err + ": " + msg

/// Solleva un'eccezione HolErr
let hol_err (err,msg) = raise (HolErr (err,msg))

/// Solleva un'eccezione HolErr exception per errori interni
let internal_err func = hol_err ("INTERNAL ERROR", func)

/// Solleva un'eccezione HolErr exception per errori di compilazione
let build_err msg = hol_err ("BUILD ERROR", msg)

//* LocalFail exception *//

/// <summary>
/// Questa eccezzione è per semplici flussi di controllo locali, sollevata per uscire 
/// dalla parte principale di una funzione e tipicamente gestita da un try-catch più  
/// esterno della stessa funzione.<para> </para> 
/// 
/// Questa può essere utile per rimuovere segnalazioni disordinate di errore 
/// dal corpo principale di una funzione e raggrupparle insieme alla 
/// fine. E' anche usata come ultima spiaggia in flussi di controllo senza errori, <para> </para> 
/// quando non c'è nulla di più elegante.
/// </summary>
exception LocalFail

(* print_exn : exn -> unit                                                    *)
(*                                                                            *)
(* This is a printer for exceptions that prints HolFails and HolErrs nicely,  *)
(* and everything else the same as normal.                                    *)
//[ndt] this part is substituted with an ovverride of the exceptions' ToString() method

/// Exception raised when an assertion fails.
/// The arguments are the location of the assert keyword in the source code (file name, line number, column number). 
exception Assert_failure of string * int * int
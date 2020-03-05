(* ========================================================================== *)
(* LEXER (HOL Zero)                                                           *)
(* - Lexer for type and term quotations                                       *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2012                            *)
(* ========================================================================== *)

(* ========================================================================== *)
(* F# Porting                                                                 *)
(*                                                                            *)
(* by Domenico Masini 2013                                                    *)
(* http://github.com/domasin/nholz                                        *)
(* ========================================================================== *)


///This module implements the lexical analysis stage, common to both HOL type
///and term quotation parsing.  The top-level type and term parsers are      
///implemented in the 'Parser' module.  The classification of characters,    
///used to determine how lexical tokens are formed, is implemented in the    
///'Names' module.           
[<AutoOpen>]                                                                                                                                                                                                                     
module HOL.Lexer

(* The lexer (like the syntax parsers) is implemented in terms of reader      *)
(* functions that take a source (in this case, a list of characters) and      *)
(* return a read item and the source correspondingly advanced, ready for the  *)
(* next item to be read.  These are in turn implemented in terms of generic   *)
(* reader utilities, defined in the 'Reader' library module.                  *)

(* ** LEXER UTILITIES ** *)


(* Specialised reader utils *)

(* These specialise the reader utilities for the case when the source is a    *)
(* list of characters.                                                        *)

let lex_char_with =
    (read_elem_with : (char -> bool) -> char list -> char * char list)

let lex_char_in =
    (read_elem_in : char list -> char list -> char * char list)

let lex_char_not_in =
    (read_elem_not_in : char list -> char list -> char * char list)

let lex_list =
    (read_list : int -> (char list -> 'a * char list) -> char list -> 'a list * char list)

let lex_end =
    (read_end : char list -> unit * char list)

(* Error handling *)

let lex_err x = hol_err ("LEXICAL ERROR", x)

let ( /+ ) read_fn msg src =
    try  read_fn src
    with ReadFail -> lex_err msg

(* ** LEXICAL TOKEN DATATYPE ** *)

(* The lexical syntax for type and term quotations consists of three basic    *)
(* classes:                                                                   *)
(*  Identifiers - for referring to names of entities;                         *)
(*  Numerics - in types: an extra form of identifier, in terms: numerals;     *)
(*  Reserved words - for syntactic sugar.                                     *)

(* Identifiers optionally carry special markings to disambiguate what they    *)
(* are referring to.  White space can be used to separate tokens, and isn't   *)
(* recorded in tokens.                                                        *)

(* Datatype definition *)

type varmark = Tyvar_mark | Tmvar_mark | No_mark

type token =
| Ident_tok of (bool * varmark * string)
| Numeric_tok of (bool * varmark * string)
| Resword_tok of string

(* Token name *)

let token_name tok =
    match tok with
    | Ident_tok (_,_,x)   -> x
    | Numeric_tok (_,_,x) -> x
    | Resword_tok x       -> x

(* ** LEXICAL ANALYSIS ** *)

(* The lexical reader functions operate on a list of characters for their     *)
(* source, reading off characters from the front of the list and grouping     *)
(* them into strings that are used to form lexical tokens.  The lexer outputs *)
(* a list of lexical tokens.                                                  *)

(* Normally, entities will have an alphanumeric or symbolic name that doesn't *)
(* clash with a reserved word, and will simply be referred to by their name.  *)
(* For entity names that are irregular or that clash with a reserved word,    *)
(* double-quote delimiters must be put around the name to disambiguate (with  *)
(* any backslash, double-quote, backquote or unprintable characters in the    *)
(* name backslash-escaped).  Such a device helps achieve parser completeness  *)
(* and printer soundness, by allowing entities to have any name without       *)
(* causing ambiguity.                                                         *)

(* Identifiers can have special markings immediately before their core name,  *)
(* to show that they refer to a particular form of entity.  A "'" mark refers *)
(* to a tyvar, and a "%" mark refers to a var.  This, again, helps achieve    *)
(* parser completeness and printer soundness, by allowing tyvars and vars     *)
(* respectively to have names of constants and type constants without causing *)
(* ambiguity.  An identifier can also be "defixed" (i.e. locally released     *)
(* from its fixity and given nonfix status) with a "$" mark (coming before    *)
(* any "'" or "%" mark).  This allows entities with fixity to occur without   *)
(* arguments.                                                                 *)


(* Token lexer *)

(* A lexical token can be an identifier, a numeric or a reserved word.        *)
(* Numerics and identifiers may have marks to distinguish their status.       *)
(*                                                                            *)
(* alphanum   =  Alphanum_char1 { Alphanum_char2 }*                           *)
(*                                                                            *)
(* symbolic   =  { Symbolic_char }+                                           *)
(*                                                                            *)
(* quote      =  Dquote                                                       *)
(*                 { Normal_char                                              *)
(*                 | Backslash ( Backslash | Dquote | Digit Digit Digit ) }*  *)
(*               Dquote                                                       *)
(*                                                                            *)
(* ident      =  { "$" }? { "'" | "%" }? ( alphanum | symbolic | quote )      *)
(*                                                                            *)
(* numeric    =  { "$" }? { "'" }? Digit { Digit | "_" }*                     *)
(*                                                                            *)
(* resword    =  Punctuation | Keyword | Enumbrkt                             *)
(*                                                                            *)
(* token      =  ident | numeric | resword                                    *)

let funcPunct (dfx,vmrk) = 
    (* Punctuation *)
    (fun c -> 
        let x = char_implode [c]
        if dfx || not (vmrk = No_mark)
        then lex_err ("Cannot mark reserved word " + quote x)
        else Resword_tok x) 
    @| 
    (lex_char_with is_punctuation_char)

let funcAlphanumeric (dfx,vmrk) = 
    (* Alphanumeric *)
    (fun (c,cs) -> 
        let x = char_implode (c::cs)
        if (is_keyword x) || (is_enum_bracket x)
        then 
            if dfx || not (vmrk = No_mark)
            then lex_err ("Cannot mark reserved word " + quote x)
            else Resword_tok x
        else Ident_tok (dfx,vmrk,x)) 
    @| 
    ((!>>>) (lex_char_with is_alphanum_char1) (lex_list 0 (lex_char_with is_alphanum_char2)))



let funcNumeric (dfx,vmrk) = 
    (* Numeric *)
    (fun (c,cs) -> 
        let x = char_implode (c::cs)
        if not (is_numeric x)
        then lex_err "Non-numeric character in numeric token"
        else if (vmrk = Tmvar_mark)
        then lex_err "Cannot mark numeric with '%'"
        else Numeric_tok (dfx,vmrk,x)) 
    @| 
    ((!>>>) (lex_char_with is_digit) (lex_list 0 (lex_char_with is_alphanum_char2)))

let funcSymbolic (dfx,vmrk) = 
    (* Symbolic *)
    (fun cs -> 
        let x = char_implode cs
        if (is_keyword x) || (is_enum_bracket x)
        then 
            if dfx || not (vmrk = No_mark)
            then lex_err ("Cannot mark reserved word " + quote x)
            else Resword_tok x
        else Ident_tok (dfx,vmrk,x)) 
    @|
    (lex_list 1 (lex_char_with is_symbolic_char))

let rec lex_token0 (dfx,vmrk) =
    (!|||) 
        (* Punctuation *)
        (funcPunct (dfx,vmrk)) 
        (
            (!|||) 
                (* Alphanumeric *)
                (funcAlphanumeric (dfx,vmrk)) 
                (
                    (!|||) 
                        (* Numeric *)
                        (funcNumeric (dfx,vmrk))
                        (
                            (!|||)
                                (* Symbolic *)
                                (funcSymbolic (dfx,vmrk))
                                (
                                    (!|||)
                                        (* Quote *)
                                        (
                                            (fun cs -> 
                                                let x = char_implode cs
                                                Ident_tok (dfx,vmrk,x)) 
                                            @|
                                            (
                                                (
                                                    lex_char_in ['"']
                                                    *>>
                                                    lex_list 0
                                                      (
                                                        (!|||)
                                                            (* Regular characters *)
                                                            (lex_char_not_in ['\\'; '"'])
                                                            (* Escape sequence *)
                                                            (
                                                                lex_char_in ['\\']
                                                                *>> 
                                                                (
                                                                    (!|||)
                                                                        (* Escaped backslash or double-quote *)
                                                                        (lex_char_in ['\\'; '"'])
                                                                        (
                                                                            (* Escape code - three decimal digits between 000 and 255 *)
                                                                            (fun ((c1,c2),c3) ->
                                                                                    let n = (int_of_string <* char_implode) [c1;c2;c3] in
                                                                                    if (n > 255)
                                                                                    then lex_err "Character escape code out of range - \
                                                                                                    must be 000 to 255"
                                                                                    else System.Convert.ToChar(n)) @|
                                                                            (
                                                                                (!>>>)
                                                                                    (
                                                                                    (
                                                                                        (!>>>)
                                                                                            (lex_char_with is_digit /+ "Invalid escape character - must be '\\', '\"' \ or ASCII code"))
                                                                                            (lex_char_with is_digit /+ "Missing escape code digits - must be 3 digits")
                                                                                    )
                                                                                    (lex_char_with is_digit /+ "Missing escape code digit - must be 3 digits")
                                                                            )
                                                                        )
                                                                )
                                                            )
                                                      )
                                                )
                                                >>* (lex_char_in ['"']  /+  "Missing closing '\"'")
                                            )
                                        )
                                        (
                                            (!|||)
                                                (* Defix mark *)
                                                (
                                                    (lex_char_in ['$']
                                                     *>> if not (vmrk = No_mark)
                                                           then fun _ -> lex_err "Defixing mark ($) must precede any var mark \
                                                                                  (' or %) in token"
                                                         else if dfx
                                                           then fun _ -> lex_err "Defixing mark ($) cannot be repeated in token"
                                                           else lex_token0 (true,vmrk))
                                                )
                                                (
                                                    (!|||)
                                                        (* Term/type var mark *)
                                                        (
                                                            (lex_char_in ['\'';'%']
                                                             *@> (fun c ->
                                                                 if not (vmrk = No_mark)
                                                                   then fun _ -> lex_err "Cannot have more than one var mark (' or %) \
                                                                                          in token"
                                                                   else let vmrk' = if (c = '%') then Tmvar_mark
                                                                                                 else Tyvar_mark in
                                                                        lex_token0 (dfx,vmrk')))
                                                                                                                      )
                                                        (* Remaining error cases *)
                                                        (
                                                            if dfx
                                                              then fun _ -> lex_err "Defix mark ($) must immediately precede name, \
                                                                                     without space"
                                                            else if not (vmrk = No_mark)
                                                              then fun _ -> lex_err "Var marks (' or %) must immediately precede name, \
                                                                                     without space"
                                                              else lex_char_with
                                                                         (fun c -> (is_unprintable_char c) && not (is_whitespace_char c))
                                                                   *@> fun c _ ->
                                                                         let n = int c in
                                                                         lex_err ("Unprintable ASCII character " + string_of_int n +
                                                                                  " - use ASCII escape code inside quotes")
                                                        )
                                                )
                                        )
                                )
                        )
                )
        )
    //TODO: manca tutta la parte sulle virgolette i caratteri di escape e altri possibili errori

let lex_token = lex_token0 (false,No_mark)

(* White space *)

(* Reads 0 or more white space chars.                                         *)

let lex_whitespace =
  lex_list 0 (lex_char_with is_whitespace_char)

(* Top-level lexer *)

let lex src = 
    fst 
        (try 
            (lex_list 0 (lex_token >>* lex_whitespace) >>* lex_end) src 
         with ReadFail -> lex_err "Undiagnosed lexical error")
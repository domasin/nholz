﻿(* ========================================================================== *)
(* NAMES (HOL Zero)                                                           *)
(* - Classification of names for parsing/printing                             *)
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


///This module provides support for classifying HOL names for the purposes of
///parsing and printing.  This consists of tests for basic classes of name   
///and commands for setting identifier fixity and enumeration brackets.  This
///module is a trusted component of the system, since it is used in the      
///implementation of the pretty printer.          
[<AutoOpen>]                                                                  
module HOL.Names

(* ** SUPPORTING DATATYPES ** *)

(* hand *)

type hand = 
    | Left 
    | Right

(* assochand *)

type assochand = 
    | LeftAssoc 
    | RightAssoc 
    | NonAssoc


(* ** BASIC NAME CLASSES ** *)


(* White space *)

(* White space characters are used for separating tokens.                     *)

(* Whitespace_char  =  Space | Tab | Line_Feed | Form_Feed | Carriage_Return  *)

let is_whitespace_char (c:char) =
  match (int c) with
    9 (* Tab *) | 10 (* Line feed *) | 12 (* Form feed *)
  | 13 (* Carriage Return *) | 32 (* Space *)
       -> true
  | _  -> false

(* Unprintable characters *)

(* These are any characters outside the ASCII range 32-126.                   *)

let is_unprintable_char (c:char) =
  (int c < 32) || (int c > 126)

(* Alphanumeric / Numeric *)

(* Alphanum_char1  =  Letter | '_'                                            *)
(* Alphanum_char2  =  Letter | Digit | '_' | '''                              *)
(*                                                                            *)
(* alphanum        =  Alphanum_char1 { Alphanum_char2 }*                      *)
(* numeric         =  Digit { Digit | '_' }*                                  *)

let is_lowercase c = ('a' <= c) && (c <= 'z')

let is_uppercase c = ('A' <= c) && (c <= 'Z')

let is_letter c = (is_lowercase c) || (is_uppercase c)

let is_digit c = ('0' <= c) && (c <= '9')

let is_alphanum_char1 c = (is_letter c) || (c = '_')

let is_alphanum_char2 c =
    (is_letter c) || (is_digit c) || (c = '_') || (c = '\'')

let is_alphanum x =
    let cs = char_explode x
    match cs with
    | c1::cs2 -> (is_alphanum_char1 c1) && (forall is_alphanum_char2 cs2)
    | []      -> false

let is_numeric x =
    let cs = char_explode x
    match cs with
    | c1::cs2 -> (is_digit c1) &&
                 (forall (fun c -> (is_digit c) || (c = '_')) cs)
    | []      -> false

(* Symbolic *)

(* Symbolic_char   =  '!' | '#' | '&' | '*' | '+' | '-' | '.' | '/'           *)
(*                  | ';' | '<' | '=' | '>' | '?' | '@'                       *)
(*                  | '[' | '\' | ']' | '^' | '{' | '|' | '}' | '~'           *)
(*                                                                            *)
(* symbolic        =  { Symbolic_char }+                                      *)

let is_symbolic_char c =
    match c with
    | '!' | '#'  | '&' | '*' | '+' | '-' | '.' | '/'
    | ';' | '<'  | '=' | '>' | '?' | '@'
    | '[' | '\\' | ']' | '^' | '{' | '|' | '}' | '~'
        -> true
    | _   -> false

let is_symbolic x =
    let cs = char_explode x
    (forall is_symbolic_char cs) && (is_nonempty cs)

(* Punctuation *)

(* Punctuation characters form one-character reserved word tokens that may be *)
(* juxtaposed, without spacing, with any other token.  The set of punctuation *)
(* characters is fixed.                                                       *)

(* Punctuation  =  '(' | ')' | ',' | ':'                                      *)

let is_punctuation_char c =
    match c with
    | '(' | ')' | ',' | ':'
        -> true
    | _  -> false

(* Keywords *)

(* Keywords are alphanumeric or symbolic reserved word tokens.  The set of    *)
(* keywords is fixed.                                                         *)

(* keyword    =  "\\" | "." | "|-"                                            *)
(*             | "if" | "then" | "else" | "let" | "and" | "in"                *)

let is_keyword x =
    match x with
    | "\\" | "." | "|-" | "if" | "then" | "else" | "let" | "and" | "in"
        -> true
    | _  -> false


(* ** FIXITY ** *)

(* Identifiers can have fixity, for giving them special syntactic status in   *)
(* type/term quotations.  Type fixity settings (see Type Fixity section)      *)
(* apply to type constants, whereas term fixity settings (see Term Fixity     *)
(* section) apply to variables and constants.                                 *)

(* Five forms of fixity are supported:                                        *)
(*  Nonfix   For no-argument entities and classic curried function            *)
(*          application.  This is the default fixity.                         *)
(*  Prefix   For unary operators that occur to the left of their single       *)
(*          argument.  These are similar to nonfix operators, but do not      *)
(*          require brackets around their argument if it is compound.  They   *)
(*          bind less tightly than nonfix.                                    *)
(*  Infix    For binary operators that occur in between their two arguments.  *)
(*          These bind less tightly than nonfix/prefix/postfix.               *)
(*  Postfix  For unary operators that occur to the right of their single      *)
(*          argument.  These bind most tightly of all operators.              *)
(*  Binder   For variable-binding operators that occur before a variable,     *)
(*          followed by '.', followed by an expression (i.e. similar to       *)
(*          lambda abstraction).  These bind least tightly of all operators.  *)

(* Infix fixities have a precedence number and an associativity hand.  The    *)
(* precedence number determines how a compound expression involving more than *)
(* one operator is read when brackets are missing, where a higher precedence  *)
(* number indicates an operator that binds more tightly.  The associativity   *)
(* hand determines how a compound expression over the same operator is read   *)
(* when brackets are missing, where a given hand indicates that the           *)
(* expression should be read as though the brackets collect at that end of    *)
(* the expression.                                                            *)

(* Note that fixities of identifiers do not have to meaningfully agree with   *)
(* the attributes of the entities that the identifiers refer to (so, for      *)
(* example, an identifier may be assigned an infix type fixity when there is  *)
(* a type constant which has that name but an arity other than 2).            *)

type fixity =
    | Nonfix
    | Prefix
    | Infix of (int * assochand)
    | Postfix
    | Binder

let precedence_ok fxty =
    match fxty with
    | Infix (n,_) -> (n > 0)
    | _           -> true

let is_nonfix_fixity fxty = (fxty = Nonfix)

let is_prefix_fixity fxty = (fxty = Prefix)

let is_infix_fixity fxty = (match fxty with  Infix _ -> true  | _ -> false)

let is_postfix_fixity fxty = (fxty = Postfix)

let is_binder_fixity fxty = (fxty = Binder)

let infix_info fxty =
    match fxty with
    | Infix (n,h) -> (n,h)
    | _           -> hol_fail ("infix_info","Not an infix fixity")

(* ** TYPE FIXITY ** *)

(* Type constant identifiers can have either infix or nonfix fixity.  By      *)
(* default, type constants without an explicitly declared fixity have nonfix  *)
(* fixity.                                                                    *)


(* Type fixity database *)

///The type fixity database registers the fixity of type constant            
///identifiers.  It is implemented as a dynamic lookup tree, indexed by type 
///constant name.  Identifiers not occurring in the database have default    
///nonfix fixity.                                                            
let the_type_fixities = ref (dltree_empty : dltree<string,fixity>)

let get_type_fixity x =
    try
        dltree_lookup x !the_type_fixities
    with HolFail _ -> Nonfix

let get_all_type_fixities() =
    let xfxtys = dltree_elems !the_type_fixities
    xfxtys

(* Type fixity inspection *)

let get_infix_type_info x =
    try
        infix_info (get_type_fixity x)
    with HolFail _ ->
        hol_fail ("get_infix_type_info",
                            "Name " + quote x + " does not have infix type fixity")

let has_nonfix_type_fixity x = is_nonfix_fixity (get_type_fixity x)

let has_infix_type_fixity x = is_infix_fixity (get_type_fixity x)

// set_type_fixity : string * fixity -> unit                                 
//                                                                           
///This is the type fixity setting command for type constant names.  It takes
///a string and a fixity, and registers the type fixity of the string name   
///as the supplied fixity, so that any type constants with that name get     
///written with that fixity.  Supplying a name that is currently registered  
///with a fixity that is not nonfix will cause failure (except in benign     
///resetting to the same fixity).  A note of the fixity change is reported,  
///and unit is returned.                                                     
let set_type_fixity (x,fxty) =
    let func = "set_type_fixity"
    assert1 ((is_infix_fixity fxty) || (is_nonfix_fixity fxty)) (func, "Type fixity must be infix or nonfix") |> ignore
    assert1 (precedence_ok fxty) (func, "Precedence must be positive") |> ignore
    try
        assert0 (get_type_fixity x = Nonfix) LocalFail |> ignore
        report ("Setting type fixity for name " + quote x) |> ignore
        match fxty with
        | Nonfix -> ()
        | _      -> the_type_fixities := dltree_insert (x,fxty) !the_type_fixities
    with LocalFail ->
        (* Benign resetting *)
        let fxty0 = get_type_fixity x
        assert1 (fxty = fxty0) (func, "Type fixity already set for name " + quote x) |> ignore
        warn ("Benign resetting of type fixity for name " + quote x)

// reset_type_fixity : string -> unit                                        
//                                                                           
///This is the type fixity resetting command for type constant names.  It    
///takes a string, and removes the registered type fixity of the string name,
///so that any type constants with that name get written with nonfix fixity. 
///A note of the fixity change is reported, and unit is returned.            
let reset_type_fixity x =
    (report ("Resetting type fixity for name " + quote x);
    the_type_fixities := dltree_delete x !the_type_fixities)

(* ** TERM FIXITY ** *)

(* Var/const identifiers can have nonfix, prefix, infix, postfix or binder    *)
(* fixity.  With infix fixity, they have a precedence and an associativity    *)
(* hand.  By default, var/const identifiers without an explicitly declared    *)
(* fixity have nonfix fixity.                                                 *)


(* Term fixity database *)

///The term fixity database registers the fixity of var/const identifiers.
///It is implemented as a dynamic lookup tree, indexed by identifier name.
///Identifiers not occurring in the database have default nonfix fixity.  
let the_fixities = ref (dltree_empty : dltree<string,fixity>)

let get_fixity x =
    try
        dltree_lookup x !the_fixities
    with HolFail _ -> Nonfix

let get_all_fixities() =
    let xfxtys = dltree_elems !the_fixities
    xfxtys

let get_infix_info x =
    try
        infix_info (get_fixity x)
    with HolFail _ ->
        hol_fail("get_infix_info","Name " + quote x + " does not have infix fixity")

let has_nonfix_fixity x = is_nonfix_fixity (get_fixity x)

let has_prefix_fixity x = is_prefix_fixity (get_fixity x)

let has_infix_fixity x = is_infix_fixity (get_fixity x)

let has_postfix_fixity x = is_postfix_fixity (get_fixity x)

let has_binder_fixity x = is_binder_fixity (get_fixity x)

(* Fixity setting commands *)

// set_fixity : string * fixity -> unit                                     
//                                                                          
///This is the term fixity setting command for variable/constant names.  It 
///takes a string and a fixity, and registers the term fixity of the string 
///name as the supplied fixity, so that any variables or constants with that
///name get written with that fixity.  Supplying a name that is currently   
///registered with a fixity that is not nonfix will cause failure (except in
///benign resetting to the same fixity).  A note of the fixity change is    
///reported, and unit is returned.                                          
let set_fixity (x,fxty) =
    let func = "set_fixity"
    assert1 (precedence_ok fxty) (func, "Precedence must be positive") |> ignore
    try
        assert0 (get_fixity x = Nonfix) LocalFail |> ignore
        report ("Setting term fixity for name " + quote x) |> ignore
        match fxty with
        | Nonfix -> ()
        | _      -> the_fixities := dltree_insert (x,fxty) !the_fixities
     with LocalFail ->
        (* Benign resetting *)
        let fxty0 = get_fixity x in
        assert1 (fxty = fxty0) (func, "Term fixity already set for " + quote x) |> ignore
        warn ("Benign resetting of term fixity for name " + quote x)

// reset_fixity : string -> unit                                             
//                                                                           
///This is the term fixity resetting command for variable/constant names.  It
///takes a string, and removes the registered term fixity of the string name,
///so that any variables or constants with that name get written with nonfix 
///fixity.  A note of the fixity change is reported, and unit is returned.
let reset_fixity x =
  (report ("Resetting term fixity for name " + quote x);
   the_fixities := dltree_delete x !the_fixities)

(* ** ENUMERATION BRACKETS ** *)

(* An enumeration expression is a serial listing of the items of some uniform *)
(* structure.  When written in term quotations, an enumeration consists of    *)
(* the items separated by commas, with delimiters called "enumeration         *)
(* brackets" at the start and end signifying the structure.                   *)
(*                                                                            *)
(*    For example, a list enumeration could be written `[ a, b, c ]` (if      *)
(*    lists were to be defined in HOL Zero), where "[" and "]" are the        *)
(*    enumeration brackets for lists.                                         *)
(*                                                                            *)
(* Internally, an enumeration expression is represented as a compound         *)
(* application of an insertion operator, inserting each item in turn into an  *)
(* empty structure constant.                                                  *)
(*                                                                            *)
(*    For example, list enumerations could be internally represented using:   *)
(*      `CONS:'a->('a)list->('a)list` for the insertion operator, and         *)
(*      `NIL:('a)list` for an empty structure constant.                       *)
(*    In which case, `[ a, b, c ]` would be internally represented as:        *)
(*      `CONS a (CONS b (CONS c NIL))`.                                       *)

(* HOL Zero provides support for the user to extend the HOL language with     *)
(* extra enumeration forms, allowing the user to specify the opening and      *)
(* closing enumeration brackets that get associated with a particular         *)
(* insertion operator and empty structure constant combination.  These        *)
(* brackets become reserved words of the HOL language, so as to avoid         *)
(* confusion with any entities with the same name.                            *)


(* Main enumeration database *)

///The main enumeration database registers the associations between          
///insertion operator and empty structure constants and opening and closing  
///enumeration brackets.  It is implemented as a dynamic lookup tree, indexed
///by empty structure constant name.                                         
let the_enum_db = ref (dltree_empty :  dltree<string, string * (string * string)>)

let get_enum_zero_op zero =
    let (z,_) = dltree_lookup zero !the_enum_db
    z

let get_enum_zero_brackets zero =
    let (_,(br1,br2)) = dltree_lookup zero !the_enum_db
    (br1, br2)

let get_all_enum_info () =
  let zys = dltree_elems !the_enum_db
  zys |> map (fun (z,(f,(br1,br2))) -> ((z, f),(br1, br2)))

(* Enumeration bracket database *)

///The enumeration bracket database is a secondary database, used during     
///parsing for looking up the empty structure constant name for a given      
///enumeration bracket.  This is implemented as a dynamic lookup tree,       
///indexed by enumeration bracket.  There are entries for each opening       
///bracket, each closing bracket and for each pair of concatenated           
///corresponding opening and closing brackets.  These concatenated pair      
///entries are used by the term quotation parser, to allow empty enumerations
///appearing in term quotations to have no space between the opening and     
///closing enumeration brackets.                                             
let the_enum_brackets = ref (dltree_empty : dltree<string, string>)

let is_enum_bracket x = (dltree_mem x !the_enum_brackets)

///Gets the closing bracket given the opning one
let get_enum_bracket_zero br =
    let z = dltree_lookup br !the_enum_brackets
    z

let is_enum_open x =
    try
        let z = get_enum_bracket_zero x
        let (br1,br2) = get_enum_zero_brackets z
        (x = br1)
    with HolFail _ -> false

let is_enum_close x =
    try
        let z = get_enum_bracket_zero x
        let (br1,br2) = get_enum_zero_brackets z
        (x = br2)
    with HolFail _ -> false

let is_enum_openclose x =
    try
        let z = get_enum_bracket_zero x
        let (br1,br2) = get_enum_zero_brackets z
        (x = br1 + br2)
    with HolFail _ -> false

(* Enumeration bracket setting command *)

let check_bracket_name br =
    let func = "set_enum_brackets"
    assert1 ((is_symbolic br) || (is_alphanum br))
            (func, quote br + " is not a valid identifier name") |> ignore
    assert1 (not (is_keyword br))
            (func, quote br + " is a keyword") |> ignore
    assert1 (not (is_enum_bracket br))
            (func, quote br + " already used for enumeration brackets") |> ignore

// set_enum_brackets : string * string -> string * string -> unit            
//                                                                           
///This is the enumeration bracket setting command.  It takes two pairs of   
///strings, where the first pair is the name of an enumeration insertion     
///operator constant and the name of an enumeration empty structure constant,
///and the second pair is the name of the opening and closing enumeration    
///brackets to be associated with these constants.  The brackets are         
///registered as the enumeration brackets corresponding to the supplied      
///constants, and become reserved words of the HOL language.  A note of the  
///bracket declaration is reported, and unit is returned.                    
let set_enum_brackets (f,zero) (br1,br2) =
    let func = "set_enum_brackets"
    try
        let br12 = br1 +  br2
        let () = assert0 (not (dltree_mem zero !the_enum_db)) LocalFail
        let _ = check_bracket_name br1
        let _ = check_bracket_name br2
        let () = assert1 (not (br1 = br2))
                            (func, "Open and close brackets must be different")
        let _ = check_bracket_name br12
        let zfs = map (fun (z,(f,_)) -> (z,f)) (dltree_elems !the_enum_db)
        let () = assert1 (cannot (inv_assoc f) zfs)
                        (func, quote f + " is already an enumeration constructor")
        (report ("Setting " + quote br1 + " and " + quote br2 +
                " as enumeration brackets for constructor " + quote f +
                " with zero " + quote zero);
        the_enum_db := dltree_insert (zero,(f,(br1,br2))) !the_enum_db;
        the_enum_brackets := dltree_insert (br1,zero) !the_enum_brackets;
        the_enum_brackets := dltree_insert (br2,zero) !the_enum_brackets;
        the_enum_brackets := dltree_insert (br12,zero) !the_enum_brackets)
    with LocalFail ->
        (* Benign resetting *)
        let (f',(br1',br2')) = dltree_lookup zero !the_enum_db in
        let () = assert1 ((f = f') && (br1 = br1') && (br2 = br2'))
                            (func, quote zero + " is already an enumeration zero") in
        warn ("Benign resetting of enumeration brackets for constructor " + quote f +
            " with zero " + quote zero)
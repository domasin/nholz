(* ========================================================================== *)
(* READER (HOL Zero)                                                          *)
(* - Library support for generic reader functions                             *)
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

///This module provides library support for generic reader functions that  
///process data from a given source and return a read item and the source  
///correspondingly advanced, ready for the next item to be read.  This gets
///used in the HOL quotation lexer and parsers (see 'Lexer' and 'Parser'   
///modules respectively).            
[<AutoOpen>]                                      
module HOL.Reader

(* ** GENERIC SOURCE ** *)

(* This section defines generic support for reader functions, placing no      *)
(* restrictions on the form of the source.                                    *)


(* Read fail exception *)

///This exception is dedicated to non-fatal failures in reader functions, and
///is used for simple control flow between reader connectives.  This allows  
///simple implementation of reader connectives that trap non-fatal failures  
///and act accordingly, whilst allowing other exceptions to propagate.
exception ReadFail

(* Post processing *)

// ( @| ) : ('b -> 'c) -> ('a -> 'b * 'a) -> 'a -> 'c * 'a
//
///Thise functions is for performing post-processing on the result of a
///reader function. The LHS is a function that reformulates the
///result of the RHS.
let ( @| ) (f:('b -> 'c)) (read_fn:('a -> 'b * 'a)) (src:'a) =
    let (x,src1) = read_fn src
    (f x, src1)

// ( @!| ) : ('b -> 'c) -> ('a -> 'b * 'a) -> 'a -> 'c
//
///These functions are for performing post-processing on the result of a  
///reader function.  The LHS is a function that produces a   
///string to get raised as an error message if the RHS succeeds.          
let ( @!| ) (f:('b -> 'c)) (read_fn:('a -> 'b * 'a)) (src:'a) =
    let (x,src') = read_fn src
    f x

(* Alternation connective *)

// ( !||| ) : ('a -> 'b) -> ('a -> 'b) -> 'a -> 'b
//
///This is for alternation.  The first reader function is tried, and if this 
///produces a ReadFail then the second reader function is tried from the same
///starting point.
let ( !||| ) read_fn1 read_fn2 src =
    try
        read_fn1 src
    with ReadFail ->
        read_fn2 src

(* Serial connectives *)

(* These connectives are for serial reading.  The first reader function reads *)
(* an initial part, and the second reader function reads the next part, with  *)
(* a ReadFail raised if either reader raises one.  The '>>>' connective       *)
(* returns the combined results as a pair, whereas '*>>' discards the first   *)
(* result, and '>>*' discards the second result.                              *)

// ( !>>> ) : ('a -> 'b * 'a) -> ('a -> 'c * 'a) -> 'a -> ('b * 'c) * 'a
//
///The first reader function reads an initial part, and the second reader 
///function reads the next part, with a ReadFail raised if either reader 
///raises one. The '>>>' connective returns the combined results as a pair
let ( !>>> ) (read_fn1:('a -> 'b * 'a)) (read_fn2:('a -> 'c * 'a)) src =
    let (x1,src') = read_fn1 src
    let (x2,src'') = read_fn2 src'
    ((x1,x2),src'')

let ( *>> ) (read_fn1:('a -> 'b * 'a)) (read_fn2:('a -> 'c * 'a)) src =
    let (x1,src') = read_fn1 src
    let (x2,src'') = read_fn2 src'
    (x2,src'')

let ( >>* ) (read_fn1:('a -> 'b * 'a)) (read_fn2:('a -> 'd * 'a)) src =
    let (x1,src') = read_fn1 src
    let (x2,src'') = read_fn2 src'
    (x1,src'')

(* Left-recursive support *)

(* These are for left-recursive cases, where alternation requires special     *)
(* consideration.  An initial part gets read by the first reader function,    *)
(* which can potentially belong to various syntactic categories.              *)

(* For '|@|', the initial part can form a stand-alone subexpression or        *)
(* optionally gets passed on as an argument to the second reader function to  *)
(* from a longer subexpression.                                               *)

let ( |@| ) (read_fn1:('a -> 'b * 'a)) (read_fn2:('b -> 'a -> 'b * 'a)) src =
    let (x1,src') = read_fn1 src in
    try
        let (x2,src'') = read_fn2 x1 src' in
        (x2,src'')
    with ReadFail -> (x1,src')

(* For '*@>', the initial part cannot form a stand-alone subexpression, and   *)
(* is passed on as an argument to the second reader function.                 *)

let ( *@> ) (read_fn1:('a -> 'b * 'a)) (read_fn2:('b -> 'a -> 'c * 'a)) src =
    let (x1,src') = read_fn1 src
    let (x2,src'') = read_fn2 x1 src'
    (x2,src'')

(* For '>@>', the initial part cannot form a stand-alone subexpression, but   *)
(* becomes the first part of the result and also is passed on as an argument  *)
(* to the second reader function.                                             *)

let ( >@> ) (read_fn1:('a -> 'b * 'a)) (read_fn2:('b -> 'a -> 'c * 'a)) src =
    let (x1,src') = read_fn1 src
    let (x2,src'') = read_fn2 x1 src'
    ((x1,x2),src'')

(* Lists *)

(* This function reads a variable-length series, of length at least 'n',      *)
(* using 'read_fn' for each element, keeping going until 'read_fn' gives a    *)
(* ReadFail, upon which it returns the successfully read elements as a list.  *)

let rec read_list n read_fn src =
  try
    let (x1,src') = read_fn src in
    let (xs2,src'') = read_list (decrement n) read_fn src' in
    (x1::xs2, src'')
  with ReadFail ->
    if (n = 0) then ([],src)
               else raise ReadFail

(* Lookahead *)

(* This function reads the next item but doesn't advance the source.          *)

let lookahead (read_fn:('a -> 'b * 'a)) src =
  let (x,_) = read_fn src in
  (x,src)

(* Various other basic reader functions *)

let read_with ((read_fn:('a -> 'b * 'a)),test_fn) src =
  let (x,src') = read_fn src in
  if (test_fn x)
    then (x,src')
    else raise ReadFail

(* ** LIST SOURCE ** *)

(* This section defines support specialised for a source in the form of a     *)
(* list.                                                                      *)


(* Head item readers *)

(* These are functions for reading the head item from a list source.          *)

let read_elem src =
  match src with
    e::src' -> (e,src')
  | _       -> raise ReadFail

let read_elem_with test_fn src =
    read_with (read_elem,test_fn) src

let read_elem_in es src =
  let test_fn e = (mem e es) in
  read_elem_with test_fn src

let read_elem_not_in es src =
  let test_fn e = not (mem e es) in
  read_elem_with test_fn src

(* Start and end *)

(* These functions respectively check that a list source isn't and is at the  *)
(* end.                                                                       *)

let read_start src =
  if (is_nonempty src)
    then ((), src)
    else raise ReadFail

let read_end src =
  if (is_empty src)
    then ((), src)
    else raise ReadFail
(* ========================================================================== *)
(* TYPES (HOL Zero)                                                           *)
(* - Datatype for internal types plus support for type constant declaration   *)
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


///This module defines the internal representation of HOL terms.  This is    
///done by defining an abstract datatype for terms, and then primitive syntax
///functions for constructing and destructing terms, and support for constant
///declaration.  The primitive syntax constructors ensure that only well-    
///formed terms can be constructed.  This module is a trusted component of   
///the system.                                                               
[<AutoOpen>]                                                                                                      
module HOL.Term

(* Also defined in this module is a primitive utility (for calculating the    *)
(* type of a term) that is needed in the definition of a primitive syntax     *)
(* function.                                                                  *)

(* ** TERM DATATYPE ** *)

(* term *)

/// <summary>
/// This is the datatype for internal HOL terms.  It has 4 classes,          
/// corresponding to the 4 primitive syntactic categories of term:<para>&#160;</para><br />       
///                                                                         
/// Variable - This denotes an occurrence of a variable.  It has name and  
/// type attributes.  Any two occurrences of variables within a given object
/// refer the same entity iff they have the same name, type and scope.<para>&#160;</para><br />     
///                                                                         
/// Constant - This denotes an occurrence of a constant.  It has name and  
/// type attributes, where the name must be a declared constant's name and  
/// the type must match the declared constant's generic type.<para>&#160;</para><br />              
///                                                                         
/// Function Application - This consists of a function subterm and an      
/// argument subterm, where the function's type must be a function type with
/// domain type equal to the argument's type.<para>&#160;</para><br />                               
///                                                                         
/// Lambda Astraction - This consists of a binding variable and a body     
/// subterm.  It bounds the scope of the binding variable to the body, and  
/// this is the only primitive means of bounding variable scope.<para>&#160;</para><br />
/// </summary>       
type term =
    | Tmvar of string * hol_type       (* variable *)
    | Tmconst of string * hol_type     (* constant *)
    | Tmcomb of term * term            (* function application *)
    | Tmabs of term * term             (* lambda abstraction *)
    with
        override this.ToString() = 
            match this with
            | Tmvar (s,htype) -> "Tmvar (\"" + s + "\", " +  htype.ToString() + ")"
            | Tmconst (s,htype) -> "Tmconst (\"" + s + "\", " +  htype.ToString() + ")"
            | Tmcomb (term1,term2) -> "Tmcomb (" + term1.ToString() + ", " +  term2.ToString() + ")"
            | Tmabs (term1,term2) -> "Tmabs (" + term1.ToString() + ", " +  term2.ToString() + ")"

(* ** CONSTANT DECLARATION ** *)

(* Constants are introduced to the theory (i.e. "declared") by supplying a    *)
(* name and a generic type.  These are then recorded in a register which can  *)
(* subsequently be queried.  A note that the declaration has taken place is   *)
(* reported, to ensure the user is kept aware of the change to the theory.    *)


(* Constant database *)

(* The constant database registers the name and generic type of all declared  *)
(* constants.  It is implemented as a dynamic lookup tree, indexed by         *)
(* constant name.                                                             *)

let the_consts = ref (dltree_empty : dltree<string,hol_type> )

// get_const_gtype : string -> hol_type                              
//                                                                   
///Returns the generic type of the constant with the supplied name. 
///Fails if the costant has not been declared
let get_const_gtype x =
    try
        dltree_lookup x !the_consts
    with HolFail _ ->
        hol_fail ("get_const_gtype", "No constant called " + quote x)

// get_all_consts : unit -> (string * hol_type) list           
//                                                             
///Returns the name and generic type of each declared constant.
let get_all_consts() =
  let xtys = dltree_elems !the_consts
  xtys

// is_const_name : string -> bool                                        
//                                                                       
///The test for whether a given name is the name of a declared constant.
let is_const_name x = (dltree_mem x !the_consts)

(* Constant declaration command *)

// prim_new_const : string * hol_type -> unit                                
//  
///<summary>                                                                         
///This is the primitive declaration command for constants.  It takes a      
///string and a type: the string becomes the name of a new constant in the  
///theory, and the type becomes its generic type.<para>&#160;</para><br />
///
///Any name can be used for a constant, but supplying an existing constant's name 
///will cause failure.<para>&#160;</para><br />
///
///A note of the declaration is reported, and unit is returned.
///</summary> 
let prim_new_const(x,ty) =
    let func = "prim_new_const"
    let () = assert1 (not (is_const_name x)) (func, "Constant name " + quote x + " already used")
    report ("Declaring constant " + quote x)
    the_consts := dltree_insert (x,ty) !the_consts

(* ** PRIMITIVE UTILITIES ** *)


(* Term comparison *)

let term_eq (x:term) y = (compare x y = 0)

let term_lt (x:term) y = (compare x y < 0)

(* Term type calculation *)

///A term's type is calculated ultimately from the types of its constituent 
///atoms.  Although potentially a derived utility, it is defined as a       
///primitive for use in 'mk_comb'.                                          
let rec type_of tm =
    match tm with
    | Tmvar (_,ty) | Tmconst (_,ty)
        -> ty
    //the type of a function application is the type of its result
    | Tmcomb (tm1,_)
        -> snd (dest_fun_type (type_of tm1)) 
    //the type of a lambda abstraction is the type of the function defined by the abstraction
    | Tmabs (v,tm0)
        -> mk_fun_type (type_of v, type_of tm0)

(* ** PRIMITIVE SYNTAX FUNCTIONS ** *)


(* Variables *)

(* The constructor for variables takes a name and a type, with no             *)
(* restrictions on these arguments.  Note that any name can be used for a     *)
(* variable, including the name of a declared constant.  Any confusion during *)
(* parsing/printing is avoided by using special markers (see 'Lexer' module). *)

///Takes a name and a type , with no restrictions on these arguments: any name 
///can be used for a variable, including the name of a declared constant.
let mk_var(x,ty) = Tmvar (x,ty)

///Takes a variable term and returns its name and type.
///Fails if the supplied term is not a variable.
let dest_var tm =
    match tm with
    | Tmvar (x,ty) -> (x,ty)
    | _            -> hol_fail ("dest_var","Not a variable")

///Checks if a term is a variable term
let is_var tm =
    match tm with
    | Tmvar _ -> true
    | _       -> false

(* Constants *)

(* Two primitive constructors for constants are defined.  Both will only      *)
(* construct a constant that has already been declared and with a type that   *)
(* matches the constant's generic type.                                       *)

///Takes a constant name that has already been declared and returns a constant 
///term. Fails if the supplied constant name has not been declared.
let mk_gconst x =
    let (x_,ty0) = try dltree_elem x !the_consts
                    with HolFail _ -> hol_fail ("mk_gconst", "No constant called " + quote x)
    Tmconst (x_,ty0)

///<summary>
///Takes a constant name and an old-to-new tyvar instantiation list, and 
///returns the constant term with its generic type's tyvars instantiated
///accordingly.<para>&#160;</para><br />
///
///Note that the instantiation domain is allowed to contain
///tyvars that are not in the generic type: these are just ignored.<para>&#160;</para><br />
///
///Fails if the constant has not been declared.
///</summary>
let mk_iconst (x,tytheta) =
  let func = "mk_iconst"
  let (x_,ty0) = try dltree_elem x !the_consts
                 with HolFail _ -> hol_fail (func, "No constant called " + quote x)
  let ty = try2 (type_inst tytheta) ty0 func
  Tmconst (x_,ty)

///Takes a constant term and returns its name and type.
///Fails if the supplied term is not a constant.
let dest_const tm =
    match tm with
    | Tmconst (x,ty) -> (x,ty)
    | _              -> hol_fail ("dest_const","Not a constant")

///Checks if a term is a constant term
let is_const tm =
    match tm with
    | Tmconst _ -> true
    | _         -> false

(* Function application *)

///<summary>
///The primitive constructor for function application checks that the type of 
///the supplied function term is a function type with a domain type equal to  
///the type of the argument term.<para>&#160;</para><br />
///
///Fails if the first term is not a function or if the domain of the function 
///is not equal to the argument type.
///</summary>
let mk_comb (tm1,tm2) =
  let func = "mk_comb"
  let (ty1,ty2) = try1 dest_fun_type (type_of tm1)
                    (func, "Arg 1 type is not a function type")
  let ty1_2 = type_of tm2
  let () = assert1 (ty1_2 = ty1)
                    (func, "Function domain type not equal to argument type")
  Tmcomb (tm1,tm2)

///Takes a function application term and returns its component terms.
///Fails if the spupplied term is not a function application.
let dest_comb tm =
    match tm with
    | Tmcomb (tm1,tm2) -> (tm1,tm2)
    | _                -> hol_fail ("dest_comb","Not a function application")

///Checks if a term is a function application term.
let is_comb tm =
    match tm with
    | Tmcomb _ -> true
    | _        -> false

(* Lambda abstraction *)

///The primitive constructor for lambda abstraction checks that the supplied
///binding variable is indeed a variable. Fails if the first term is not 
///a variable term                                  
let mk_abs (v,tm0) =
    assert1 (is_var v) ("mk_abs","Arg 1 is not a variable") |> ignore
    Tmabs (v,tm0)

///Takes a lambda abstraction term and returns its component terms.
///Fails if the supplied term is not a lambda abstraction.
let dest_abs tm =
    match tm with
    | Tmabs (v,tm0) -> (v,tm0)
    | _             -> hol_fail ("dest_abs","Not a lambda abstraction")

///Checks if a term is a function application term.
let is_abs tm =
    match tm with
    | Tmabs _ -> true
    | _       -> false
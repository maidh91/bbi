(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

type t =
| Atom of string
| Top
| Bot
| Unit
| Neg of t
| And of t * t
| Or of t * t
| Imply of t * t
| Star of t * t
| Wand of t * t
  with sexp

(* module Reader : *)
(* sig *)
(*   val from_string : string -> t *)
(* end *)
(*   = *)
(* struct *)
(*   open Genlex *)

(*   let lexer = make_lexer ["("; ")"; "T"; "F"; "I"; "!"; "/\\"; "\\/"; "->"; "-*"; "*"];; *)

(*   let rec parse_atom_prop = parser *)
(*     | [< 'Ident s >] -> Atom s *)
(*     | [< 'Kwd "T" >] -> Top *)
(*     | [< 'Kwd "F" >] -> Bot *)
(*     | [< 'Kwd "I" >] -> Unit *)
(*     | [< 'Kwd "("; prop_A = parse_prop; 'Kwd ")" >] -> prop_A *)

(*   and parse_neg_prop = parser *)
(*     | [< 'Kwd "!"; prop_A = parse_atom_prop >] -> Neg prop_A *)
(*     | [< prop_A = parse_atom_prop >] -> prop_A *)

(*   and parse_and_prop = parser *)
(*     | [< prop_A = parse_neg_prop; prop_A' = parse_and_prop_aux prop_A >] -> prop_A' *)

(*   and parse_and_prop_aux prop_A = parser *)
(*     | [< 'Kwd "/\\"; prop_B = parse_and_prop >] -> And (prop_A, prop_B) *)
(*     | [< 'Kwd "*"; prop_B = parse_and_prop >] -> Star (prop_A, prop_B)  *)
(*     | [< >] -> prop_A *)

(*   and parse_or_prop = parser *)
(*     | [< prop_A = parse_and_prop; prop_A' = parse_or_prop_aux prop_A >] -> prop_A' *)

(*   and parse_or_prop_aux prop_A = parser *)
(*     | [< 'Kwd "\\/"; prop_B = parse_or_prop >] -> Or (prop_A, prop_B) *)
(*     | [< >] -> prop_A *)

(*   and parse_imply_prop = parser *)
(*     | [< prop_A = parse_or_prop; prop_A' = parse_imply_prop_aux prop_A >] -> prop_A' *)

(*   and parse_imply_prop_aux prop_A = parser *)
(*     | [< 'Kwd "->"; prop_B = parse_imply_prop >] -> Imply (prop_A, prop_B) *)
(*     | [< 'Kwd "-*"; prop_B = parse_imply_prop >] -> Wand (prop_A, prop_B) *)
(*     | [< >] -> prop_A *)

(*   and parse_prop = parser  *)
(*     | [< prop_A = parse_imply_prop >] -> prop_A *)

(*   let from_string s = parse_prop (lexer (Stream.of_string s)) *)
(* end *)


module Reader :
sig
  val from_string : string -> t
end
  =
struct
  open Genlex

  let lexer = make_lexer ["("; ")"; "T"; "F"; "I"; "!"; "/\\"; "\\/"; "->"; "-*"; "*"];;

  let rec parse_atom_prop = parser
    | [< 'Ident s >] -> Atom s
    | [< 'Kwd "T" >] -> Top
    | [< 'Kwd "F" >] -> Bot
    | [< 'Kwd "I" >] -> Unit
    | [< 'Kwd "("; prop_A = parse_prop; 'Kwd ")" >] -> prop_A

  and parse_neg_prop = parser
    | [< 'Kwd "!"; prop_A = parse_neg_prop >] -> Neg prop_A
    | [< prop_A = parse_atom_prop >] -> prop_A

  and parse_and_prop = parser
    | [< prop_A = parse_and_prop_left (fun a -> a) >] -> prop_A
      
  and parse_and_prop_left cont = parser
    | [< prop_A = parse_neg_prop; prop_B = parse_and_prop_aux (cont prop_A) >] -> prop_B
      
  and parse_and_prop_aux prop_A = parser
    | [< 'Kwd "/\\"; prop = parse_and_prop_left (fun b -> And(prop_A,b)) >] -> prop
    | [< 'Kwd "*"; prop = parse_and_prop_left (fun b -> Star(prop_A,b)) >] -> prop
    | [< >] -> prop_A
      
  and parse_or_prop = parser
    | [< prop_A = parse_or_prop_left (fun a -> a) >] -> prop_A

  and parse_or_prop_left cont = parser
    | [< prop_A = parse_and_prop; prop_B = parse_or_prop_aux (cont prop_A) >] -> prop_B

  and parse_or_prop_aux prop_A = parser
    | [< 'Kwd "\\/"; prop = parse_or_prop_left (fun b -> Or(prop_A,b)) >] -> prop
    | [< >] -> prop_A

  and parse_imply_prop = parser
    | [< prop_A = parse_or_prop; prop_A' = parse_imply_prop_aux prop_A >] -> prop_A'

  and parse_imply_prop_aux prop_A = parser
    | [< 'Kwd "->"; prop_B = parse_imply_prop >] -> Imply (prop_A, prop_B)
    | [< 'Kwd "-*"; prop_B = parse_imply_prop >] -> Wand (prop_A, prop_B)
    | [< >] -> prop_A

  and parse_prop = parser 
    | [< prop_A = parse_imply_prop >] -> prop_A

  let escape_neg str =
    Core.Core_string.split str ~on:'!'
    |! Core.Core_string.concat ~sep:" !"

  let from_string s = parse_prop (lexer (Stream.of_string (escape_neg s)))
end

module Writer :
sig
  val to_string : t -> string
  val to_tex : t -> string
end 
  =
struct
    (* Check if /child/ has lower precedence than /parent/ *)
    (* let need_bracket parent child = *)
  let ofPrecedence = function
    | Neg _ -> 1
    | And _ 
    | Star _ -> 3
    | Or _ -> 4
    | Imply _
    | Wand _ -> 5
    | _ -> 0 
    (* in *)
    (* ofPrecedence parent < ofPrecedence child *)
      
  let rec to_string_aux parent_prec child =
    let child_prec = ofPrecedence child in
    let child_prec_assoc = child_prec - 1 in
    let needBracket = parent_prec < child_prec in
    let partial =
      match child with
      | Atom s -> s
      | Top -> "T"
      | Bot -> "F"
      | Unit -> "I"
      | Neg t -> "!" ^ (to_string_aux child_prec t)
      | And (t1, t2) -> 
        (to_string_aux child_prec t1) ^ "/\\" ^ (to_string_aux child_prec_assoc t2)
      | Or (t1, t2) -> 
        (to_string_aux child_prec t1) ^ "\\/" ^ (to_string_aux child_prec_assoc t2)
      | Imply (t1, t2) -> 
        (to_string_aux child_prec_assoc t1) ^ "->" ^ (to_string_aux child_prec t2)
      | Star (t1, t2) -> 
        (to_string_aux child_prec t1) ^ "*" ^ (to_string_aux child_prec_assoc t2)
      | Wand (t1, t2) -> 
        (to_string_aux child_prec_assoc t1) ^ "-*" ^ (to_string_aux child_prec t2)
    in
    if needBracket then "("^partial^")" else partial

  let to_string prop = to_string_aux 100 prop

    (* TODO: Functorize it *)
  let rec to_tex_aux parent_prec child =
    let child_prec = ofPrecedence child in
    let child_prec_assoc = child_prec - 1 in
    let needBracket = parent_prec < child_prec in
    let partial =
      match child with
      | Atom s -> s
      | Top -> "\\Ttop"
      | Bot -> "\\Tbot"
      | Unit -> "\\Tunit"
      | Neg t -> "\\Tneg{" ^ (to_tex_aux child_prec t) ^ "}"
      | And (t1, t2) -> 
        "\\Tand{" ^ (to_tex_aux child_prec t1) ^ "}{" ^ (to_tex_aux child_prec_assoc t2) ^ "}"
      | Or (t1, t2) -> 
        "\\Tor{" ^ (to_tex_aux child_prec t1) ^ "}{" ^ (to_tex_aux child_prec_assoc t2) ^ "}"
      | Imply (t1, t2) -> 
        "\\Timply{" ^ (to_tex_aux child_prec_assoc t1) ^ "}{" ^ (to_tex_aux child_prec t2) ^ "}"
      | Star (t1, t2) -> 
        "\\Tstar{" ^ (to_tex_aux child_prec t1) ^ "}{" ^ (to_tex_aux child_prec_assoc t2) ^ "}"
      | Wand (t1, t2) -> 
        "\\Twand{" ^ (to_tex_aux child_prec_assoc t1) ^ "}{" ^ (to_tex_aux child_prec t2) ^ "}"
    in
    if needBracket then "("^partial^")" else partial

  let to_tex prop = to_tex_aux 100 prop
end

(** Extraction functions for Prop.t *) 
let match_prop_fails (expected : string) (given_prop : t) =
  String.concat ["A proposition of the form "; expected; " is expected, ";
                 "but "; Writer.to_string given_prop; " is given."] 
  |! wrap_err

let match_prop_neg = function
  | Neg prop_A -> wrap prop_A
  | prop -> match_prop_fails "!A" prop

let match_prop_and = function
  | And (prop_A, prop_B) -> wrap (prop_A, prop_B)
  | prop -> match_prop_fails "A /\\ B" prop

let match_prop_or = function
  | Or (prop_A, prop_B) -> wrap (prop_A, prop_B)
  | prop -> match_prop_fails "A \\/ B" prop

let match_prop_imply = function
  | Imply (prop_A, prop_B) -> wrap (prop_A, prop_B)
  | prop -> match_prop_fails "A -> B" prop

let match_prop_star = function
  | Star (prop_A, prop_B) -> wrap (prop_A, prop_B)
  | prop -> match_prop_fails "A * B" prop

let match_prop_wand = function
  | Wand (prop_A, prop_B) -> wrap (prop_A, prop_B)
  | prop -> match_prop_fails "A -* B" prop

let match_prop_neg_exn prop = match_prop_neg prop |! simpl_unwrap
let match_prop_and_exn prop = match_prop_and prop |! simpl_unwrap
let match_prop_or_exn prop = match_prop_or prop |! simpl_unwrap
let match_prop_imply_exn prop = match_prop_imply prop |! simpl_unwrap
let match_prop_star_exn prop = match_prop_star prop |! simpl_unwrap
let match_prop_wand_exn prop = match_prop_wand prop |! simpl_unwrap


(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

exception NotImplemented
  
module Error :
sig
  val fails : string -> string
end

type 'a result =
| Ok of 'a
| Error of string

val wrap : 'a -> 'a result
val wrap_err : string -> 'a result

val exn_failure : string -> 'a
val exn_wrap_err : ?msg:string -> exn -> 'a result
val exn_reraise : ?msg:string -> exn -> 'a

val merge_result : 'a result -> 'b result -> ('a * 'b) result
val merge_result_pair : 'a result * 'b result -> ('a * 'b) result
val merge_result_list : 'a result list -> 'a list result

val rewrap_err : 'a result -> 'b result
val unwrap : string -> 'a result -> 'a
val unwrap_lazy : (unit -> string) -> 'a result -> 'a
val simpl_unwrap : 'a result -> 'a
val wrap_option : ?msg:string -> 'a option -> 'a result
val wrap_bool : ?msg:string -> bool -> bool result
val ( >> ) : 'a result -> ('a -> 'b result) -> 'b result
val ( >| ) : 'a result -> ('a -> 'b) -> 'b result
val ( |!> ) : 'a -> ('a -> 'b) -> 'b result

module World :
sig
  type t with sexp
  type rename = (t, t) Core.Std.Map.t with sexp

  val get_fresh : unit -> t
  val reset : unit -> unit

  val eq : t -> t -> bool
  val compare : t -> t -> int

  val rename : rename -> ?msg:string -> t -> t result
  val rename_exn : rename -> ?msg:string -> t -> t

  val to_string : t -> string
  val to_tex : t -> string
  val rename_to_string : rename -> string
end

module type RULE =
sig
  type t    with sexp
  type seq  with sexp
end

module type PROOF =
sig
  type rule with sexp
  type seq  with sexp

  type t = rule * seq * premise
  and premise =
  | PUnit
  | POne of t
  | PTwo of t * t
  with sexp;;

  val match_prem_unit : premise -> unit result          
  val match_prem_one : premise -> t result
  val match_prem_two : premise -> (t * t) result

  val match_prem_unit_exn : premise -> unit
  val match_prem_one_exn : premise -> t
  val match_prem_two_exn : premise -> (t * t) 

  val seq_of : t -> seq
end

module ProofFn (Rule : RULE) : PROOF
  with type rule = Rule.t and type seq = Rule.seq

val eq_assoc_list : ('a * 'b) list -> ('a * 'b) list -> bool
(* val eq_list : 'a list -> 'a list -> bool *)
val eq_list : 'a list -> 'a list -> unit result
val diff_list : 'a list -> 'a list -> 'a list * 'a list
val diff_assoc_list : ('a * 'b) list -> ('a * 'b) list  -> ('a * 'b) list * ('a * 'b) list

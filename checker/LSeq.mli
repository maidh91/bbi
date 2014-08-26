(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Common
open Core.Std

type world_rel = {
  parent : World.t;
  lchild : World.t;
  rchild : World.t;
}
with sexp

type wstate =
| Prop of Prop.t
| Mzero
with sexp
    
type t = {
  worlds : World.t list;
  relations : world_rel list;
  tcontext : (wstate * World.t) list;
  fcontext : (Prop.t * World.t) list;
}
with sexp

(* Main operations on a sequent*)
(* Make sure given two sequent are equivalent. *)
val eq : t -> t -> unit result
val merge : t -> t -> t result
val apply_rename : World.rename -> t -> t result
val syntactic_well_formed : t -> unit result

(* Printing function: Optional function arguments are for indicating which elements to highlight *)
val to_tex :
  ?w_highlight:(World.t -> bool) ->
  ?rel_highlight:(world_rel -> bool) ->
  ?tc_highlight:((wstate * World.t) -> bool) ->
  ?fc_highlight:((Prop.t * World.t) -> bool) ->
  t -> string

(* Auxiliary operations on a sequent *)
(* These functions do not guarantee the the well-formedness of the result sequent. *)
(* However, they still check the validity of the given argument(s) for debugging purpose. *)
val create :
  ?rc: world_rel list ->
  ?tc: (wstate * World.t) list ->
  ?fc: (Prop.t * World.t) list ->
  World.t list -> t
  
(* Make sure that a given argument indeed appears in the sequent. *)
val exists_wc : World.t -> t -> unit result
val exists_rc : world_rel -> t -> unit result
val exists_tc_prop : Prop.t * World.t -> t -> unit result
val exists_tc_mzero : World.t -> t -> unit result
val exists_fc : Prop.t * World.t -> t -> unit result

(* Add a given argument to the sequent only if the argument is valid *)
val add_wc : World.t -> t -> t result                 (* World.t is fresh world. *)
val add_rc : world_rel -> t -> t result               (* world_rel is a relation between existing worlds. *)
val add_tc_prop : Prop.t * World.t -> t -> t result   (* World.t exists. *)
val add_tc_mzero : World.t -> t -> t result           (* World.t exists. *)
val add_fc : Prop.t * World.t -> t -> t result        (* World.t exists. *)

(* Remove a given argument from the sequent only if the argument exists in the sequent. *)
val remove_wc : World.t -> t -> t result
(* Note that removal of World.t breaks the validity of the sequent. *)
val remove_rc : world_rel -> t -> t result
val remove_tc_prop : Prop.t * World.t -> t -> t result
val remove_tc_mzero : World.t -> t -> t result
val remove_fc : Prop.t * World.t -> t -> t result


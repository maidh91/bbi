(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

type state =
| Prop of Prop.t
| Mzero             (* multiplicative zero *)
with sexp

type wstate =
| Mpair of t * t    (* multiplicative pair *)
| Apair of t * t    (* adjoint pair *)

and t = {
  world : World.t;
  tcontext : state list;   
  fcontext : Prop.t list; 
  wcontext : wstate list;
}
with sexp

(* Main operations on a sequent*)
val eq : t -> t -> unit result
val merge : t -> t -> t result
val apply_rename : World.rename -> t -> t result
val syntactic_well_formed : t -> unit result

(* Printing function: Optional function arguments are for indicating which elements to highlight *)
val to_tex :
  ?w_highlight:(World.t -> bool) ->
  ?tc_highlight:(state -> bool) ->
  ?fc_highlight:(Prop.t -> bool) ->
  t -> string

(* Auxiliary operations on a sequent *)
(* These functions do not guarantee the the well-formedness of the result sequent. *)
(* However, they still check the validity of the given argument(s) for debugging purpose. *)

val create : ?tc:state list -> ?fc:Prop.t list -> ?wc:wstate list -> World.t -> t

val exists_wc_mpair : (World.t * World.t) -> t -> unit result
val exists_wc_apair : (World.t * World.t) -> t -> unit result
val exists_tc_prop : Prop.t -> t -> unit result
val exists_tc_mzero : t -> unit result
val exists_fc : Prop.t -> t -> unit result

val pick_wc : (wstate -> bool) -> t -> (wstate * t) result
val pick_wc_exn : (wstate -> bool) -> t -> wstate * t
val pick_wc_mpair : (World.t * World.t) -> t -> ((t * t) * t) result
val pick_wc_apair : (World.t * World.t) -> t -> ((t * t) * t) result

(** 'add' functions *)
val add_wc : wstate -> t -> t result
val add_wc_mpair : (t * t) -> t -> t result           (* Check freshness. *)
val add_wc_apair : (t * t) -> t -> t result           (* Check freshness. *)
val add_tc_prop : Prop.t -> t -> t result
val add_tc_mzero : t -> t result
val add_fc : Prop.t -> t -> t result

val add_wc_exn : wstate -> t -> t
val add_wc_mpair_exn : (t * t) -> t -> t 
val add_wc_apair_exn : (t * t) -> t -> t
val add_tc_prop_exn : Prop.t -> t -> t
val add_tc_mzero_exn : t -> t 
val add_fc_exn : Prop.t -> t -> t

(** 'remove' functions *)
val remove_wc_mpair : (World.t * World.t) -> t -> t result
val remove_wc_apair : (World.t * World.t) -> t -> t result
val remove_tc_prop : Prop.t -> t -> t result
val remove_tc_mzero : t -> t result  (* delete only one? *)
val remove_fc : Prop.t -> t -> t result

val remove_wc_mpair_exn : (World.t * World.t) -> t -> t
val remove_wc_apair_exn : (World.t * World.t) -> t -> t
val remove_tc_prop_exn : Prop.t -> t -> t
val remove_tc_mzero_exn : t -> t (* delete only one? *)
val remove_fc_exn : Prop.t -> t -> t

(** collect all world names *)
val collect_world_names : t -> World.t list

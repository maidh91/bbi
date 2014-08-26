(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Common

type priority = Pri_zero | Pri_one

type local_seq = {
  ew: int;                              (* the number of multZero *)

  rc : (World.t * World.t * priority) list;

  tc_n : Prop.t list;                   (* truth context *)
  tc_r : Prop.t list;
  tc_s : Prop.t list;
  tc_d : Prop.t list;

  fc_n : Prop.t list;                   (* falsehood context *)
  fc_r : Prop.t list;
  fc_s : Prop.t list;
  fc_d : Prop.t list;
}

(* rc : a pair of world names of a child relation and its priority *)

(* tc_n, fc_n: Not yet considered formulas. *)
(* tc_r: Once considered and no need to be considered again when
 *       consider a truth context.
 *       ie. tc_r:Atomic, Top, Unit / fc_r:Atomic, Bottom, Unit *)
(* tc_s: Once considered but need to be considered again. 
 *       ie. ts_s:Wand / fc_s:Star *)
(* tc_d: Once considered and disappeared formulas. 
 *       ie. tc_d: Neg, Imply, And, Or, Star 
 *           fc_d: Neg, Imply, And, Or, Wand 
 *)

(* ew + tc_n + tc_r + tc_s + tc_d : All formulas which have introduced to the node. *)
(* ew + tc_n + tc_r + tc_s : Current formulas. *)
(* ew + tc_r + tc_s + tc_d : Once considered formulas. *)

type seq = {
  all: (World.t * (local_seq * priority)) list;
}
(* label, description, priority *)


val eq: seq -> seq -> unit result
val empty_ls : local_seq

(* Converter *)
val of_lseq: LSeq.t -> seq
val to_lseq: seq -> LSeq.t

val get_nth_w : int -> seq -> World.t
val get_nth_rc : int -> int -> seq -> (World.t * World.t * priority)
val get_nth_tc : int -> int -> seq -> Prop.t
val get_nth_fc : int -> int -> seq -> Prop.t

val find_nth_rc : int -> (World.t * World.t * priority -> bool) -> seq -> (World.t * World.t * priority)
val find_parent : (World.t * World.t) -> seq -> World.t

val is_empty : World.t -> seq -> bool
val is_hidden : World.t -> seq -> bool

val is_hidden_rel : World.t -> (World.t * World.t) -> seq -> bool

val exists_rc : World.t -> (World.t * World.t) -> seq -> bool
val exists_tc : World.t -> Prop.t -> seq -> bool
val exists_fc : World.t -> Prop.t -> seq -> bool

val find_ls : seq -> World.t -> local_seq

val comm_rc : World.t -> (World.t * World.t) -> seq -> seq

val del_w : seq -> World.t -> seq
val del_rc : World.t -> (World.t * World.t) -> seq -> seq
val del_tc : World.t -> Prop.t -> seq -> seq
val del_fc : World.t -> Prop.t -> seq -> seq

val append_ws : (World.t * (local_seq * priority)) list -> seq -> seq
val cons_w: (World.t * (local_seq * priority)) -> seq -> seq
val add_rc : World.t -> (World.t * World.t * priority) -> seq -> seq
val add_tc : World.t -> Prop.t -> seq -> seq
val add_fc : World.t -> Prop.t -> seq -> seq
val add_ew : World.t -> seq -> seq

val mark_tc_r : World.t -> Prop.t -> seq -> seq
val mark_fc_r : World.t -> Prop.t -> seq -> seq
val mark_tc_s : World.t -> Prop.t -> seq -> seq
val mark_fc_s : World.t -> Prop.t -> seq -> seq

val merge_local_seq : local_seq -> local_seq -> local_seq
val merge_seq : seq -> seq -> seq

val make_rename : ?rule:(World.t->World.t) -> seq -> World.rename
val apply_rename : World.rename -> seq -> seq

(* hide all child relations in each node of ws & hide node itself *)
val hide_ws : World.t list -> seq -> seq
(* hide selected relation *)
val hide_rc : World.t -> (World.t * World.t) -> seq -> seq
(* val reveal_ws : World.t list -> seq -> seq *)

val visible_worlds : seq -> World.t list
val hidden_worlds : seq -> World.t list
val all_worlds : seq -> World.t list

(* Pretty printer *)
val to_string : ?show_hidden:bool -> seq -> string

(* Printer helper function *)
val get_ls_idx : seq -> World.t -> int
val get_rc_idx : seq -> int -> World.t * World.t -> int
val get_tc_idx : seq -> int -> Prop.t -> int
val get_fc_idx : seq -> int -> Prop.t -> int

(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

(* The following code is modified from Coq 8.3. *)

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Proof_tree
open Proof_type

(* val inter_rule_to_rule : goal -> inter_rule -> rule *)
val refiner_inter : inter_rule -> tactic
val refiner : rule -> tactic
val app_tac : tactic -> proof_tree -> proof_tree

(* [frontier : proof_tree -> goal list * validation]
   given a proof [p], [frontier p] gives [(l,v)] where [l] is the list of goals
   to be solved to complete the proof, and [v] is the corresponding
   validation *)
val frontier : proof_tree -> (goal list * validation)

(* [list_pf p] is the lists of goals to be solved in order to complete the
   proof [p] *)
val list_pf : proof_tree -> goal list

(* [frontier_map f n p] applies f on the n-th open subgoal of p and
   rebuilds proof-tree.
   n=1 for first goal, n negative counts from the right *)
val frontier_map :
  (proof_tree -> proof_tree) -> int -> proof_tree -> proof_tree

(* [frontier_mapi f p] applies (f i) on the i-th open subgoal of p. *)
val frontier_mapi :
  (int -> proof_tree -> proof_tree) -> proof_tree -> proof_tree

val leaf : goal -> proof_tree

(* Functions for handling the state of the proof editor. *)

type pftreestate

val mk_pftreestate : goal -> pftreestate
val mk_pftreestate_pf : proof_tree -> pftreestate

val proof_of_pftreestate : pftreestate -> proof_tree
val cursor_of_pftreestate : pftreestate -> int list
val is_top_pftreestate : pftreestate -> bool
val is_complete_pftreestate : pftreestate -> bool
val top_goal_of_pftreestate : pftreestate -> goal
val nth_goal_of_pftreestate : int -> pftreestate -> goal

val traverse : int -> pftreestate -> pftreestate
val map_pftreestate : (proof_tree -> proof_tree) -> pftreestate -> pftreestate
val solve_nth_pftreestate : int -> tactic -> pftreestate -> pftreestate
val solve_pftreestate : tactic -> pftreestate -> pftreestate

(* a weak version of logical undoing *)
val weak_undo_pftreestate : pftreestate -> pftreestate

exception Not_found_pf of string

val first_unproven : pftreestate -> pftreestate
val last_unproven : pftreestate -> pftreestate
val nth_unproven : int -> pftreestate -> pftreestate
val next_unproven : pftreestate -> pftreestate
val prev_unproven : pftreestate -> pftreestate
val top_of_tree : pftreestate -> pftreestate
val up_until_cursor : int list -> pftreestate -> pftreestate

(* Pretty-printers. *)
val pftreestate_to_string_simple : pftreestate -> string
val pftreestate_to_string : ?show_hidden:bool -> pftreestate -> string


(* for statistics *)
val num_of_call_solve_pftreestate : unit -> Big_int.big_int
val reset_num_of_call_solve_pftreestate : unit -> unit
val solve_pftreestate_count : tactic -> pftreestate -> pftreestate

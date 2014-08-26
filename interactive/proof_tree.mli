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

open Proof_type

val mk_goal : Seq.seq -> goal

val rule_of_proof   : proof_tree -> inter_rule
val serialize_rules : proof_tree -> inter_rule list
val ref_of_proof      : proof_tree -> (inter_rule * proof_tree list)
val children_of_proof : proof_tree -> proof_tree list
val goal_of_proof     : proof_tree -> goal
val status_of_proof   : proof_tree -> int
val is_complete_proof : proof_tree -> bool
val is_leaf_proof     : proof_tree -> bool

(* Conversion *)
val to_lproof : proof_tree -> LBBI.Proof.t
val rule_to_inter_rule: Seq.seq -> rule -> inter_rule

(* Pretty printer *)
val pr_goal : ?show_hidden:bool -> goal -> string
val pr_proof_tree : ?show_hidden:bool -> proof_tree -> string
val pr_proof_tree_rules : proof_tree -> string

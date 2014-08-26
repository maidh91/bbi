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

open Common

type proof_tree = {
  open_subgoals : int;
  goal : goal;
  ref : (inter_rule * proof_tree list) option }

and inter_rule =
| RInit of (World.t * Prop.t * Prop.t)
| RTopR of (World.t * Prop.t)
| RBotL of (World.t * Prop.t)
| RNegL of (World.t * Prop.t)
| RNegR of (World.t * Prop.t)
| RAndL of (World.t * Prop.t)
| RAndR of (World.t * Prop.t)
| ROrL of (World.t * Prop.t)
| ROrR of (World.t * Prop.t)
| RImplyL of (World.t * Prop.t)
| RImplyR of (World.t * Prop.t)
| RUnitL of (World.t * Prop.t)
| RUnitR of (World.t * Prop.t)
| RStarL of ((World.t * Prop.t) * (World.t * World.t))
| RStarR of (World.t * (World.t * World.t) * Prop.t) 
| RWandL of (World.t * (World.t * World.t) * Prop.t) 
| RWandR of ((World.t * Prop.t) * (World.t * World.t))
| RComm of (World.t * (World.t * World.t))
| RAssoc of ((World.t * World.t * World.t * World.t * World.t) * (World.t * World.rename * World.rename * World.rename)) (* w, w', w1, w2, w3 *)
| RZeroU of (World.t * (World.t * World.rename))
| RZeroD of (World.t * (World.t * World.t) * World.rename)

and rule =
| Init of (int * int * int)               (* local_seq idx * tc idx * fc idx*)
| TopR of (int * int)                     (* local_seq idx * fc idx *)
| BotL of (int * int)                     (* local_seq idx * tc idx *)
| NegL of (int * int)                     (* local_seq idx * tc idx *)
| NegR of (int * int)                     (* local_seq idx * fc idx *)
| AndL of (int * int)                     (* local_seq idx * tc idx *)
| AndR of (int * int)                     (* local_seq idx * fc idx *)
| OrL of (int * int)                      (* local_seq idx * tc idx *)
| OrR of (int * int)                      (* local_seq idx * fc idx *)
| ImplyL of (int * int)                   (* local_seq idx * tc idx *)
| ImplyR of (int * int)                   (* local_seq idx * fc idx *)
| UnitL of (int * int)                    (* local_seq idx * tc idx *)
| UnitR of (int * int)                    (* local_seq idx * fc idx *)
| StarL of (int * int)                    (* local_seq idx * tc idx *)
| WandR of (int * int)                    (* local_seq idx * fc idx *)
| Comm of (int * int)                     (* local_seq idx * rc idx *)
| ZeroU of int                            (* local_seq idx *)
| ZeroD of (int * int)                    (* local_seq idx(w) * local_seq idx(w1) *)
| StarR of (int * int * int)              (* local_seq idx(w) * rc idx(w1-w2) * fc idx(star) *)
| WandL of (int * int * int)              (* local_seq idx(w) * tc idx(wand) * local_seq idx(w1) *)
| Assoc of (int * int * int)              (* local_seq idx(w1) * local_seq idx(w2) * local_seq idx(w3) *)

and goal = Seq.seq

and tactic = goal -> (goal list * validation)

and validation = (proof_tree list -> proof_tree)


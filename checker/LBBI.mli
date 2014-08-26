(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

module Rule : sig
  val id : string

  type seq = LSeq.t with sexp

  type premise =
  | PUnit
  | POne of seq
  | PTwo of seq * seq
  with sexp

  val match_prem_unit : premise -> unit result
  val match_prem_one : premise -> seq result
  val match_prem_two : premise -> (seq * seq) result

  val match_prem_unit_exn : premise -> unit
  val match_prem_one_exn : premise -> seq
  val match_prem_two_exn : premise -> (seq * seq) 

  type t =
  | Init of (Prop.t * World.t) 
  | TopR of World.t 
  | BotL of World.t 
  | NegL of (Prop.t * World.t) 
  | NegR of (Prop.t * World.t) 
  | AndL of (Prop.t * World.t) 
  | AndR of (Prop.t * World.t) 
  | OrL of (Prop.t * World.t) 
  | OrR of (Prop.t * World.t) 
  | ImplyL of (Prop.t * World.t) 
  | ImplyR of (Prop.t * World.t) 
  | UnitL of World.t 
  | UnitR of World.t 
  | StarL of (Prop.t * World.t) * (World.t * World.t)
  | StarR of (LSeq.world_rel * Prop.t) 
  | WandL of (LSeq.world_rel * Prop.t) 
  | WandR of (Prop.t * World.t) * (World.t * World.t)
  | Comm of LSeq.world_rel
  | Assoc of (LSeq.world_rel * LSeq.world_rel) * (World.t * World.rename * World.rename * World.rename)
  | ZeroU of World.t * (World.t * World.rename)
  | ZeroD of LSeq.world_rel * World.rename
  with sexp

  val valid_seq : seq -> unit result

  val forward : t -> premise -> seq result
  (* ''forward rule premise'' returns a unique result sequent by applying ''rule'' on the ''premise''. *)
  (* If there is no premise(PUnit), forward fails because the result sequent is not unique. *)
  (* This function is for converter. *)
    
  val backward : t -> seq -> premise result
  (* ''backward rule seq'' infers premise(s) from ''rule'' on the goal sequent ''seq''. *)
  (* If the rule requires no premise, it returns PUnit. *)
  (* This function is for certifier. *) 

  val rule_to_tex_command: t -> string
  val seq_to_tex: t -> seq -> string
  val seq_eq : seq -> seq -> unit result
end

module Proof : PROOF with type rule = Rule.t and type seq = Rule.seq

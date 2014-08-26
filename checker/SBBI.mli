(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

module Rule : sig
  val id : string

  type seq = WSeq.t with sexp

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

  type split = {
    selected_tc: WSeq.state list;
    selected_fc: Prop.t list;
    selected_wc: (World.t * World.t) list;
  }
  with sexp

  type t =
  | Init
  | TopL
  | TopR
  | BotL
  | BotR
  | NegL of Prop.t 
  | NegR of Prop.t 
  | AndL of Prop.t 
  | AndR of Prop.t * split
  | OrL of Prop.t * split
  | OrR of Prop.t 
  | ImplyL of Prop.t * split
  | ImplyR of Prop.t 
  | UnitL
  | UnitR
  | StarL of Prop.t * (World.t * World.t)
  | StarR
  | WandL
  | WandR of Prop.t * (World.t * World.t)
  | TC of (World.t * World.t)
  | TP of (World.t * World.t)
  | WeakL of WSeq.state
  | WeakR of Prop.t
  | WeakW of (World.t * World.t)        (* Weakening for Mpair/Apair *)
  | ContraL of WSeq.state
  | ContraR of Prop.t 
  | ContraW of (World.t * World.t * World.rename)
  | Comm of (World.t * World.t)
  | Assoc of (World.t * World.t) * World.t
  | ZeroU of split * (World.t * World.t)
  | ZeroD of (World.t * World.t)
  with sexp

  val valid_seq : seq -> unit result

  val forward : t -> premise -> seq result
  val backward : t -> seq -> premise result  

  val apply_split : split -> seq -> (seq * seq) result

  val rule_to_tex_command: t -> string
  val seq_to_tex: t -> seq -> string
  val seq_eq: seq -> seq -> unit result
end

module Build : sig
  type desc = 
  | Init of World.t * Prop.t
  | TopL 
  | TopR of World.t
  | BotL of World.t
  | BotR
  | NegL of Prop.t
  | NegR of Prop.t
  | AndL of Prop.t
  | AndR of Prop.t
  | OrL of Prop.t
  | OrR of Prop.t
  | ImplyL of Prop.t
  | ImplyR of Prop.t
  | UnitL  
  | UnitR of World.t
  | StarL of Prop.t * (World.t * World.t)
  | StarR of World.t * Prop.t
  | WandL of World.t * Prop.t
  | WandR of Prop.t * (World.t * World.t)
  | TC of (World.t * World.t)
  | TP of (World.t * World.t)
  | WeakL of WSeq.state
  | WeakR of Prop.t
  | WeakW of WSeq.wstate
  | ContraL of WSeq.state
  | ContraR of Prop.t
  | ContraW of (World.t * World.t) * World.rename
  | Comm of (World.t * World.t)
    (* Assoc ((w_1, w_new), w_1n2) *)
  | Assoc of ((World.t * World.t) * World.t)
  | ZeroU of (World.t * World.t)
  | ZeroD of (World.t * World.t * Rule.split)
  with sexp

  val forward : desc -> Rule.premise -> (Rule.t * Rule.seq) result
end

module Proof : PROOF with type rule = Rule.t and type seq = Rule.seq

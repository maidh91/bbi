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

  type t =
  | Init of Prop.t 
  | TopR
  | BotL
  | NegL of Prop.t 
  | NegR of Prop.t 
  | AndL of Prop.t 
  | AndR of Prop.t 
  | OrL of Prop.t 
  | OrR of Prop.t 
  | ImplyL of Prop.t 
  | ImplyR of Prop.t 
  | UnitL
  | UnitR
  | StarL of Prop.t * (World.t * World.t)
  | StarR of ((World.t * World.t) * Prop.t) 
  | WandL of ((World.t * World.t) * Prop.t) 
  | WandR of Prop.t * (World.t * World.t)
  | TC of (World.t * World.t) 
  | TP of (World.t * World.t) 
  | Comm of (World.t * World.t) 
  (* 
     Assoc (((w', w_3), (w_1, w_2)), (w_new, rn_1, rn_2, rn_3)) is applicable to
     w: \Gamma; W', (w_3 : \Gamma_3 => \Delta_3) => \Delta
     where W' = (w': \Gamma'; (w_1: \Gamma_1 => \Delta_1), (w_2: \Gamma_2 => \Delta_2) => \Delta').
  *)
  | Assoc of ((World.t * World.t) * (World.t * World.t)) * (World.t * World.rename * World.rename * World.rename)
  | ZeroU of unit * (World.rename * World.t)
  | ZeroD of (World.t * World.t) * World.rename
  with sexp

  val valid_seq : seq -> unit result
  val forward : t -> premise -> seq result
  val backward : t -> seq -> premise result

  val rule_to_tex_command: t -> string
  val seq_to_tex: t -> seq -> string
  val seq_eq: seq -> seq -> unit result
end

module Proof : PROOF with type rule = Rule.t and type seq = Rule.seq

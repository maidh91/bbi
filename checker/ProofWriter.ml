(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

module type SPEC =
sig
  module Rule :    
  sig
    type t with sexp
    type seq with sexp
    type premise =
    | PUnit                               (* of ??? *)
    | POne of seq
    | PTwo of seq * seq
    with sexp

    val rule_to_tex_command: t -> string
    val seq_to_tex: t -> seq -> string
    val seq_eq: seq -> seq -> unit result
  end

  module Proof :
  sig
    type t = Rule.t * Rule.seq * premise
    and premise =
      | PUnit
      | POne of t
      | PTwo of t * t
    with sexp;;
  end
end

module type S =
sig
  type proof

  val to_tex : proof -> string
  (* val to_html : proof -> string *)
end

module Make (Spec : SPEC) =
struct
  type proof = Spec.Proof.t

  let rec to_tex (rule, seq, premise) = 
    let rule_name = Spec.Rule.rule_to_tex_command rule in
    let goal_seq = Spec.Rule.seq_to_tex rule seq in
    let premise_string =
      match premise with
      | Spec.Proof.PUnit -> "\n"
      | Spec.Proof.POne proof1 -> (to_tex proof1)
      | Spec.Proof.PTwo (proof1, proof2) -> (to_tex proof1) ^ "&\n" ^ (to_tex proof2) in
    "\\infer[" ^ rule_name ^ "]\n"
    ^ "{" ^ goal_seq ^ "}\n"
    ^ "{" ^ premise_string ^ "}\n"

  (* let rec to_html (rule, seq, premise) = *)
  (*   let rule_name = Spec.Rule.rule_to_tex_command rule in *)
  (*   let goal_seq = Spec.Rule.seq_to_tex rule seq in *)
  (*   let premise_string = *)
  (*     match premise with *)
  (*     | Spec.Proof.PUnit -> "\n" *)
  (*     | Spec.Proof.POne proof1 -> (to_tex proof1) *)
  (*     | Spec.Proof.PTwo (proof1, proof2) -> (to_tex proof1) ^ "&\n" ^ (to_tex proof2) in *)
  (*   "\\infer[" ^ rule_name ^ "]\n" *)
  (*   ^ "{" ^ goal_seq ^ "}\n" *)
  (*   ^ "{" ^ premise_string ^ "}\n" *)

end

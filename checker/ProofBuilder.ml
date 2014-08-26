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
    val id : string
      
    type t with sexp
    type seq with sexp
    type premise =
    | PUnit
    | POne of seq
    | PTwo of seq * seq
    with sexp

    val forward : t -> premise -> seq result
  end

  module Proof :
  sig
    type t = Rule.t * Rule.seq * premise
    and premise =
    | PUnit
    | POne of t
    | PTwo of t * t
    with sexp
  end 
end

module type S =
sig
  type proof
  type premise
  type rule

  val construct : rule -> premise -> proof result
  val construct_exn : rule -> premise -> proof
end

module Make (Spec : SPEC) =
struct
  type proof = Spec.Proof.t with sexp
  type premise = Spec.Proof.premise with sexp
  type rule = Spec.Rule.t with sexp

  let goal_of (_, seq, _) = seq

  let forward_exn rule prem = Spec.Rule.forward rule prem |! simpl_unwrap

  let construct rule prem = 
    (* try *)
      match prem with
      | Spec.Proof.PUnit ->
        raise NotImplemented
      | Spec.Proof.POne lproof ->
        wrap (rule, forward_exn rule (Spec.Rule.POne (goal_of lproof)), prem)
      | Spec.Proof.PTwo (proof_1, proof_2) ->
        wrap (rule, forward_exn rule (Spec.Rule.PTwo (goal_of proof_1, goal_of proof_2)), prem)
    (* with e -> *)
    (*   let msg = String.concat [Error.fails (Spec.Rule.id ^ ".convert")] *)
    (*    (\*                        Spec.Proof.sexp_of_premise prem |! Sexp.to_string_hum]  *\) in *)
    (*   wrap_err msg *)
                               
  let construct_exn rule prem = construct rule prem |! simpl_unwrap 
end

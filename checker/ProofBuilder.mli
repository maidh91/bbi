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

module Make (Spec : SPEC) : S
  with type proof = Spec.Proof.t
  and type premise = Spec.Proof.premise
  and type rule = Spec.Rule.t

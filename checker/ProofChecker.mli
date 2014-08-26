(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Common

module type SPEC =
sig
  module Rule :
  sig
    val id : string
      
    type t with sexp
    type seq with sexp
    type premise =
    | PUnit                               (* of ??? *)
    | POne of seq
    | PTwo of seq * seq
    with sexp
        
    val valid_seq : seq -> unit result

    val backward : t -> seq -> premise result

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

  val certify : proof -> unit result
  val certify_exn : proof -> unit
end

module Make (Spec : SPEC) : S
  with type proof = Spec.Proof.t

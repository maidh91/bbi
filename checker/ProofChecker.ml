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

module Make (Spec : SPEC) =
struct
  type proof = Spec.Proof.t

  let rec certify_aux depth prev_rule prev_seq (rule, seq, premise) expected_seq =
    let depth = depth + 1 in

    let suffix () = 
      String.concat [" at depth "; string_of_int depth; "\n\n";
                     "Prev rule:\n\n"; Option.sexp_of_t Spec.Rule.sexp_of_t prev_rule 
                     |! Sexp.to_string_hum; "\n\n";
                     "Prev sequent:\n\n"; Option.sexp_of_t Spec.Rule.sexp_of_seq prev_seq 
                     |! Sexp.to_string_hum; "\n\n";                     
                     "Given rule:\n\n"; Spec.Rule.sexp_of_t rule |! Sexp.to_string_hum; "\n\n";
                     "Given sequent:\n\n"; Spec.Rule.sexp_of_seq seq |! Sexp.to_string_hum; "\n\n";
                     "Expected sequent:\n\n"; Spec.Rule.sexp_of_seq expected_seq 
                     |! Sexp.to_string_hum; "\n"] in

    Spec.Rule.valid_seq seq
    |! unwrap_lazy (fun () -> "Sequent is not valid :" ^ (suffix ()));

    Spec.Rule.seq_eq seq expected_seq
    |! unwrap_lazy (fun () -> "Expected sequent is not equivalent to actual sequent." ^ (suffix ()));

    let expected_premise_seq = 
      Spec.Rule.backward rule seq
      |! unwrap_lazy (fun () -> "Rule is not applicable on the goal sequent:" ^ (suffix ())) in 
    
    match expected_premise_seq, premise with
    | Spec.Rule.PUnit, Spec.Proof.PUnit -> ()
    | Spec.Rule.POne (exp_seq1), Spec.Proof.POne proof1 -> 
      certify_aux depth (Some rule) (Some seq) proof1 exp_seq1
    | Spec.Rule.PTwo (exp_seq1,exp_seq2), Spec.Proof.PTwo (proof1, proof2) -> 
      certify_aux depth (Some rule) (Some seq) proof1 exp_seq1; 
      certify_aux depth (Some rule) (Some seq) proof2 exp_seq2
    | _ -> wrap_err ("# of Expected premise - # of premise mismatch") |! simpl_unwrap
        
  let certify ((_, seq, _) as proof) = 
    try 
      certify_aux 0 None None proof seq |! wrap
    with e -> exn_wrap_err ~msg:(Error.fails (Spec.Rule.id ^ ".certify")) e
  let certify_exn proof = certify proof |! simpl_unwrap
end

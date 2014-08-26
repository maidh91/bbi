(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Common

val convert : LBBI.Proof.t -> CSBBI.Proof.t result
val convert_exn : LBBI.Proof.t -> CSBBI.Proof.t

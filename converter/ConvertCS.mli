(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Common

val convert : CSBBI.Proof.t -> SBBI.Proof.t result
val convert_exn : CSBBI.Proof.t -> SBBI.Proof.t

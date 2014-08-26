(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Proof_tree
open Proof_type
open Refiner

exception Auto_fail

val solve_inv: pftreestate -> pftreestate
val auto_dfs: depth:int -> pftreestate -> pftreestate

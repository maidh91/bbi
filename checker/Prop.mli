(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Common

type t =
| Atom of string
| Top
| Bot
| Unit
| Neg of t
| And of t * t
| Or of t * t
| Imply of t * t
| Star of t * t
| Wand of t * t
  with sexp
      
val match_prop_neg : t -> t result
val match_prop_and : t -> (t * t) result
val match_prop_or : t -> (t * t) result
val match_prop_imply : t -> (t * t) result
val match_prop_star : t -> (t * t) result
val match_prop_wand : t -> (t * t) result

val match_prop_neg_exn : t -> t 
val match_prop_and_exn : t -> (t * t) 
val match_prop_or_exn : t -> (t * t) 
val match_prop_imply_exn : t -> (t * t) 
val match_prop_star_exn : t -> (t * t) 
val match_prop_wand_exn : t -> (t * t) 

module Reader : 
sig 
  val from_string : string -> t 
end

module Writer :
sig 
  val to_string : t -> string 
  val to_tex : t -> string 
end

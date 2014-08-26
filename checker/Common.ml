(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std;;

exception NotImplemented

module Debug =
struct
  (*
     print_sexp : ('a -> Sexp.t) -> 'a -> unit
     print_diff : ('a -> Sexp.t) -> 'a -> 'a -> unit
  *)
  let print_sexp f x = f x |! Sexp.to_string_hum |! print_string |! print_newline
  let print_diff f exp_e given_e = raise NotImplemented
end

module Error =
struct
  let err_header id = String.concat ["Error in "; id; ":"]
  let add_header id msg = String.concat [err_header id; "\n"; msg]
  
  (** Error messages *)
  let fails id = err_header id
end

type 'a result =
  | Ok of 'a
  | Error of string

let wrap a = Ok a
let wrap_err msg = Error msg

let merge_msg ?(msg="") msg' = if String.is_empty msg then msg' else msg ^ "\n" ^ msg'

let exn_failure s = raise (Failure s)

let exn_wrap_err ?(msg="") = function
  | Failure msg' -> merge_msg ~msg:msg msg' |! wrap_err
  (* | e -> raise e *)
  | e -> merge_msg ~msg:msg (Exn.sexp_of_t e |! Sexp.to_string_hum) |! wrap_err

let exn_reraise ?(msg="") = function
  | Failure msg' -> merge_msg ~msg:msg msg' |! exn_failure
  | e -> merge_msg ~msg:msg (Exn.sexp_of_t e |! Sexp.to_string_hum) |! exn_failure
  (* | e -> raise e *)

(* 'a result -> 'b result -> ('a * 'b) result *)
let merge_result a b =
  match a, b with
    | Ok a', Ok b' -> Ok (a', b')
    | Ok _, Error err -> Error err
    | Error err, Ok _ -> Error err
    | Error err1, Error err2 -> Error (err1 ^ "\n" ^ err2)

let merge_result_pair (a, b) = merge_result a b

(* 'a result list -> 'a list result *)
let merge_result_list l =
  match List.partition_map l ~f:(function Ok a -> `Fst a | Error b -> `Snd b) with
    | a, [] -> Ok a
    | _, err -> Core.Std.String.concat ~sep:"\n" err |! wrap_err

let rewrap_err = function
  | Ok _ -> assert false
  | Error err -> Error err

(* string -> 'a result -> 'a *)
let unwrap msg r  =
  match r with
  | Ok a -> a
  | Error msg' -> merge_msg ~msg:msg msg' |! exn_failure

let unwrap_lazy msg_f r =
  match r with
  | Ok a -> a
  | Error msg' -> merge_msg ~msg:(msg_f ()) msg' |! exn_failure

let simpl_unwrap r  =
  match r with
  | Ok a -> a
  | Error msg -> raise (Failure msg)

let wrap_option ?(msg="") = function
  | Some a -> Ok a
  | None -> Error msg

let wrap_bool ?(msg="") = function
  | true -> Ok true
  | false -> Error msg

(* val (>>) : 'a result -> ('a -> 'b result) -> 'b result *)
let (>>) (m : 'a result) (f : 'a -> 'b result) =
  match m with
  | Ok v -> f v
  | Error msg -> Error msg

(* val (>|) : 'a result -> ('a -> 'b) -> 'b result *)
let (>|) (m : 'a result) (f : 'a -> 'b) =
  match m with
  | Ok v -> Ok (f v)
  | Error msg -> Error msg

(* 'a -> ('a -> 'b) -> 'b result *)
let (|!>) (v : 'a) (f : 'a -> 'b) = f v |! wrap

module type IDENT =
sig
  type t with sexp
  type rename = (t, t) Map.t with sexp

  val eq : t -> t -> bool
  val compare : t -> t -> int
  val to_string : t -> string
  val to_tex : t -> string
  val get_fresh : unit -> t
  val reset : unit -> unit
  val rename : rename -> ?msg:string -> t -> t result
  val rename_exn : rename -> ?msg:string -> t -> t
  val rename_to_string : rename -> string
end

module IdentFn (S : sig val id : string end) : IDENT =
struct
  type t = int
  with sexp
  type rename = (t, t) Map.t
  with sexp

  let eq s s' = s = s'
  let to_string v = S.id ^ string_of_int v
  let to_tex v = S.id ^ "_{" ^ string_of_int v ^ "}"
  let compare v1 v2 = v1 - v2
  let cnt = ref 0
  let get_fresh () =
        let v = !cnt in
        incr cnt; v
  let reset () = cnt := 0
  let rename map ?(msg="") label =
    Map.find map label |! wrap_option ~msg:("World.rename: " ^ msg ^ (to_string label) ^ " is not found")
  let rename_exn map ?(msg="") label = rename map ~msg:msg label |! simpl_unwrap
  let rename_to_string rename =
    Map.sexp_of_t sexp_of_t sexp_of_t rename |! Sexp.to_string_hum
    (* Map.fold (fun ~key ~data aux -> aux ^ ", " ^  *)
    (* val fold : f:(key:key -> data:'a -> 'b -> 'b) -> *)
    (*    'a t -> init:'b -> 'b *)
end

module World = IdentFn (struct let id = "w" end)

module type RULE =
sig
  type t with sexp
  type seq with sexp
end

module type PROOF =
sig
  type rule with sexp
  type seq with sexp

  type t = rule * seq * premise
  and premise =
  | PUnit
  | POne of t
  | PTwo of t * t
  with sexp;;

  val match_prem_unit : premise -> unit result          
  val match_prem_one : premise -> t result
  val match_prem_two : premise -> (t * t) result

  val match_prem_unit_exn : premise -> unit
  val match_prem_one_exn : premise -> t
  val match_prem_two_exn : premise -> (t * t) 

  val seq_of : t -> seq
end
      
module ProofFn (Rule:RULE) =
struct
  type rule = Rule.t with sexp
  type seq = Rule.seq with sexp

  type t = Rule.t * Rule.seq * premise
  and premise =
  | PUnit
  | POne of t
  | PTwo of t * t
  with sexp

  let match_prem_unit = function
    | PUnit -> wrap ()
    | _ -> wrap_err "PUnit is expected, but isn't given."

  let match_prem_one = function
    | POne proof -> wrap proof
    | _ -> wrap_err "POne is expected, but isn't given."
      
  let match_prem_two = function
    | PTwo (proof_l, proof_r) -> wrap (proof_l, proof_r)
    | _ -> wrap_err "PTwo is expected, but isn't given."

  let match_prem_unit_exn prem = match_prem_unit prem |! simpl_unwrap
  let match_prem_one_exn prem = match_prem_one prem |! simpl_unwrap
  let match_prem_two_exn prem = match_prem_two prem |! simpl_unwrap

  let seq_of (_, seq, _) = seq
end

(* let rec eq_assoc_list l_1 l_2 = *)
(*   match l_1, l_2 with *)
(*   | (li, content) :: l_1', _ :: _ -> begin *)
(*     match List.Assoc.find l_2 li with *)
(*     | Some content' when content' = content -> *)
(*       eq_assoc_list l_1' (List.Assoc.remove l_2 li) *)
(*     | _ -> false *)
(*   end *)
(*   | [], [] -> true *)
(*   | _ -> false *)
    
(* let rec eq_list l_1 l_2 = *)
(*   let rec remove e = function *)
(*     | [] -> [] *)
(*     | hd :: tl -> if hd = e then tl else hd :: (remove e tl) *)
(*   in *)
(*   match l_1, l_2 with *)
(*   | hd_1 :: tl_1, _ :: _ -> begin *)
(*     match List.find ~f:((=) hd_1) l_2 with *)
(*     | Some hd_2 -> eq_list tl_1 (remove hd_2 l_2) *)
(*     | None -> wrap_err "eq_list: l_1 and l_2 are not equivalent" *)
(*   end *)
(*   | [], [] -> wrap () *)
(*   | [], _ -> wrap_err "eq_list: l_2 is bigger than l1" *)
(*   | _, [] -> wrap_err "eq_list: l_1 is bigger than l2" *)

let rec eq_list_aux l1 l2 =
  match l1, l2 with
  | hd1::l1', hd2::l2' ->
    if hd1 = hd2 then eq_list_aux l1' l2'
    else wrap_err "eq_list: l_1 and l_2 are not equivalent"
  | [], [] -> wrap ()
  | [], _ -> wrap_err "eq_list: l_2 is bigger than l1"
  | _, [] -> wrap_err "eq_list: l_1 is bigger than l2"

let eq_list l_1 l_2 = 
  let l_1s = List.sort l_1 ~cmp:Pervasives.compare in
  let l_2s = List.sort l_2 ~cmp:Pervasives.compare in
  eq_list_aux l_1s l_2s

let cmp_pair (key1,v1) (key2,v2) =
  let key_compare = Pervasives.compare key1 key2 in
  if key_compare <> 0 then key_compare
  else Pervasives.compare v1 v2

let rec eq_assoc_list l_1 l_2 =
  let l_1s = List.sort l_1 ~cmp:cmp_pair in
  let l_2s = List.sort l_2 ~cmp:cmp_pair in
  try 
    eq_list_aux l_1s l_2s |! simpl_unwrap;
    true
  with _ -> false

let diff_list l_1 l_2 =
  let l_1s = List.sort l_1 ~cmp:Pervasives.compare in
  let l_2s = List.sort l_2 ~cmp:Pervasives.compare in
  let rec remove e = function
    | [] -> []
    | hd :: tl -> if hd = e then tl else hd :: (remove e tl) in
  let rec eq_aux l1fail l_1 l_2 =
    match l_1, l_2 with
    | hd_1 :: l_1', _ :: _ -> begin
      match List.find ~f:((=) hd_1) l_2 with
      | Some hd_2 -> eq_aux l1fail l_1' (remove hd_2 l_2)
      | _ -> eq_aux (hd_1::l1fail) l_1' l_2
    end
    | l1remain, l2remain -> (List.rev_append l1remain l1fail, l2remain)
  in
  eq_aux [] l_1s l_2s

let diff_assoc_list l_1 l_2 =
  let l_1s = List.sort l_1 ~cmp:cmp_pair in
  let l_2s = List.sort l_2 ~cmp:cmp_pair in
  let rec eq_aux l1fail l_1 l_2 =
    match l_1, l_2 with
    | ((li, content) as elem) :: l_1', _ :: _ -> begin
      match List.Assoc.find l_2 li with
      | Some content' when content' = content ->
        eq_aux l1fail l_1' (List.Assoc.remove l_2 li)
      | _ -> eq_aux (elem::l1fail) l_1' l_2
    end
    | l1remain, l2remain -> (List.rev_append l1remain l1fail), l2remain
  in
  eq_aux [] l_1s l_2s

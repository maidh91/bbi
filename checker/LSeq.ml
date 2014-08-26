(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

type world_rel = {
  parent:World.t;
  lchild:World.t;
  rchild:World.t;
}
with sexp

type wstate =
| Prop of Prop.t
| Mzero             (* multiplicative zero *)
with sexp

type t = {
  worlds : World.t list;
  relations : world_rel list;
  tcontext : (wstate * World.t) list;
  fcontext : (Prop.t * World.t) list;
}
with sexp

(***************************************************************)
(* Main operations on a sequent *)
(***************************************************************)
let eq seq1 seq2 =
  try
    eq_list seq1.worlds seq2.worlds
    |! unwrap "Worlds do not agree.";
    eq_list seq1.relations seq2.relations
    |! unwrap "Relations do not agree.";
    eq_list seq1.tcontext seq2.tcontext
    |! unwrap "Tcontext do not agree.";
    eq_list seq1.fcontext seq2.fcontext
    |! unwrap "Fcontext do not agree.";
    wrap ()
  with
  | e -> exn_wrap_err ~msg:("LSeq.eq Failed.") e
    
(* TODO: wrap && To do well-formed check? *)
let merge seq1 seq2 =
  wrap { worlds = List.rev_append seq1.worlds seq2.worlds;
         relations = List.rev_append seq1.relations seq2.relations;
         tcontext = List.rev_append seq1.tcontext seq2.tcontext;
         fcontext = List.rev_append seq1.fcontext seq2.fcontext;
       }

let diff seq1 seq2 =
  let w1, w2 = diff_list seq1.worlds seq2.worlds in
  let rel1, rel2 = diff_list seq1.relations seq2.relations in
  let t1, t2 = diff_list seq1.tcontext seq2.tcontext in
  let f1, f2 = diff_list seq1.fcontext seq2.fcontext in
  { worlds = w1; relations = rel1; tcontext = t1; fcontext = f1},
  { worlds = w2; relations = rel2; tcontext = t2; fcontext = f2}

let apply_rename wrename seq = 
  let wrename = World.rename wrename in
  let relrename {parent=p; lchild=lc; rchild=rc} = 
    match wrename p, wrename lc, wrename rc with
    | Ok newp, Ok newlc, Ok newrc -> 
      wrap ({parent=newp; lchild=newlc; rchild=newrc})
    | a, b, c -> 
      merge_result a b |! merge_result c |! rewrap_err in
  let lrename (wstate, w) = 
    match wrename w with
    | Ok neww ->
      wrap (wstate, neww)
    | Error msg -> wrap_err msg in
  let rrename (prop, w) = 
    match wrename w with
    | Ok neww ->
      wrap (prop, neww)
    | Error msg -> wrap_err msg in
  let w_result = List.map seq.worlds ~f:wrename |! merge_result_list in
  let rel_result = List.map seq.relations ~f:relrename |! merge_result_list in
  let l_result = List.map seq.tcontext ~f:lrename |! merge_result_list in
  let r_result = List.map seq.fcontext ~f:rrename |! merge_result_list in
  match w_result, rel_result, l_result, r_result with
  | Ok w, Ok rel, Ok l, Ok r -> wrap {worlds=w; relations=rel; tcontext=l; fcontext=r}
  | a, b, c, d -> merge_result a b |! merge_result c |! merge_result d |! rewrap_err

(***************************************************************)
(* val syntactic_well_formed: t -> bool *)
(* 1. Worlds are all distinct *)
(* 2. Worlds collected from relations, truth context, and falsehood context appear in kai. *)
(***************************************************************)

(* TODO: wrap *)
let syntactic_well_formed {worlds=ws; relations=rel; tcontext=tc; fcontext=fc} =
  try
    (* All labels in each context are distinct *)
    List.exn_if_dup 
      ~compare:World.compare 
      ~context:"All worlds must be distinct."
      ws 
      ~to_sexp:World.sexp_of_t;
    (* worlds collected from relations, tc, and fc are equivalent to kai *)
      let worlds_from_rel = rel |! List.concat_map
          ~f:(fun {parent=p; lchild=l; rchild=r} -> [p;l;r]) in
      let worlds_from_tc = tc |! List.split |! snd in
      let worlds_from_fc = fc |! List.split |! snd in
      let (err_ws, err_context) =
        worlds_from_rel
        |! List.rev_append worlds_from_tc
        |! List.rev_append worlds_from_fc
        |! List.dedup ~compare:World.compare
        |! diff_list ws in
      match err_context with
      | [] -> wrap ()
      | w::_ -> wrap_err ("Some worlds in the context are invalid: " ^ World.to_string w) |! simpl_unwrap
  with
  | List.Duplicate_found (dup, msg) ->
    wrap_err ("syntactic_well_formed failed.\n"
              ^ msg ^ " But "
              ^ (dup () |! Sexp.to_string_hum))
  | e -> exn_wrap_err ~msg:("syntactic_well_formed failed.") e

(***************************************************************)
(* Printer function *)
(***************************************************************)
let to_tex_relation {parent=p; lchild=l; rchild=r} =
  "\\Bequiv{" ^ (World.to_tex p) ^ "}{\\Wmul{" ^ (World.to_tex l) ^ "}{" ^ (World.to_tex r) ^ "}}"

let to_tex_tcontext_aux = function
  | (Prop prop, w) -> ("\\Btrue{" ^ (World.to_tex w) ^ "}{" ^ (Prop.Writer.to_tex prop) ^ "}")
  | (Mzero, w) -> ("\\Btrue{" ^ (World.to_tex w) ^ "}{\\multzero}")

let to_tex_fcontext_aux (prop, w) =
  "\\Btrue{" ^ (World.to_tex w) ^ "}{" ^ (Prop.Writer.to_tex prop) ^ "}"

let dummy_highlight = fun elem -> false

let to_tex_list_aux ?(highlight = dummy_highlight) ?(delim = ", ") printer = function
  | [] -> "\\cdot"
  | r::rlist ->
    let printer elem = if highlight elem then "\\fbox{$"^(printer elem)^"$}" else (printer elem) in
    List.fold_left ~f:(fun aux elem -> aux ^ delim ^ (printer elem))  ~init:(printer r) rlist

let to_tex ?(w_highlight = dummy_highlight)
    ?(rel_highlight = dummy_highlight)
    ?(tc_highlight = dummy_highlight)
    ?(fc_highlight = dummy_highlight)
    {worlds=w; relations=r; tcontext=t; fcontext=f} =
  (* let worlds    = to_tex_list_aux ~highlight:w_highlight World.to_tex w in *)
  let relations = to_tex_list_aux ~highlight:rel_highlight to_tex_relation r in
  let tcontext  = to_tex_list_aux ~highlight:tc_highlight to_tex_tcontext_aux t in
  let fcontext  = to_tex_list_aux ~highlight:fc_highlight to_tex_fcontext_aux f in
  "\\Jbblseq{" ^ (* worlds ^ ";~" ^ *) relations ^ "}{" ^ tcontext ^ "}{" ^ fcontext ^ "}"


(***************************************************************)
(* Auxiliary operations on a sequent *)
(***************************************************************)
let create ?(rc = []) ?(tc = []) ?(fc = []) wc = { worlds = wc; relations = rc; tcontext = tc; fcontext = fc }

(* let get_l_wc lseq = lseq.worlds *)
(* let get_l_rc lseq = lseq.relations *)
(* let get_l_tc lseq = lseq.tcontext *)
(* let get_l_fc lseq = lseq.fcontext *)

let exists_wc w lseq =
  if List.mem w lseq.worlds then wrap ()
  else wrap_err (World.to_string w ^ " is not found.")

let exists_rc rel lseq = 
  if List.mem rel lseq.relations then wrap ()
  else wrap_err ((sexp_of_world_rel rel |! Sexp.to_string_hum) ^ " is not found.")

let exists_tc_prop (prop, world) lseq = 
  if List.mem (Prop prop, world) lseq.tcontext then wrap ()
  else wrap_err ((Prop.Writer.to_string prop) ^ "@" ^ (World.to_string world) ^ " is not found.")

let exists_tc_mzero world lseq = 
  if List.mem (Mzero, world) lseq.tcontext then wrap ()
  else wrap_err ("Mzero@" ^ (World.to_string world) ^ " is not found.")

let exists_fc (prop, world) lseq = 
  if List.mem (prop, world) lseq.fcontext then wrap ()
  else wrap_err ((Prop.Writer.to_string prop) ^ "@" ^ (World.to_string world) ^ " is not found.")

(* let find_rc_exn ci lseq = find_rc ci lseq |! simpl_unwrap  *)
(* let find_tc_exn li lseq = find_tc li lseq |! simpl_unwrap  *)
(* let find_fc_exn ri lseq = find_fc ri lseq |! simpl_unwrap  *)

let add_wc w lseq =
  if List.mem w lseq.worlds then
    wrap_err (World.to_string w ^ " is already in the sequent.")
  else wrap { lseq with worlds = w::lseq.worlds }

let add_rc ({parent=pw; lchild=lw; rchild=rw} as rel) lseq =
  if not (List.mem pw lseq.worlds) then
    wrap_err (World.to_string pw ^ " is invalid world.")
  else if not (List.mem lw lseq.worlds) then
    wrap_err (World.to_string lw ^ " is invalid world.")
  else if not (List.mem rw lseq.worlds) then
    wrap_err (World.to_string rw ^ " is invalid world.")
  else wrap { lseq with relations = rel::lseq.relations }

let add_tc_prop (prop, w) lseq =
  if not (List.mem w lseq.worlds) then
    wrap_err (World.to_string w ^ " is invalid world.")
  else wrap { lseq with tcontext = (Prop prop,w):: lseq.tcontext }

let add_tc_mzero w lseq =
  if not (List.mem w lseq.worlds) then
    wrap_err (World.to_string w ^ " is invalid world.")
  else wrap { lseq with tcontext = (Mzero,w) :: lseq.tcontext }

let add_fc (prop, w) lseq =
  if not (List.mem w lseq.worlds) then
    wrap_err (World.to_string w ^ " is invalid world.")
  else wrap { lseq with fcontext = (prop,w) :: lseq.fcontext }

(* (\* let add_wc_exn w lseq = add_wc w lseq |! simpl_unwrap  *\) *)
(* (\* let add_rc_exn ci rel lseq = add_rc ci rel lseq |! simpl_unwrap  *\) *)
(* (\* let add_tc_prop_exn li (prop, w) lseq = add_tc_prop li (prop, w) lseq |! simpl_unwrap  *\) *)
(* (\* let add_tc_mzero_exn li w lseq = add_tc_mzero li w lseq |! simpl_unwrap  *\) *)
(* (\* let add_fc_exn ri (prop, w) lseq = add_fc ri (prop, w) lseq |! simpl_unwrap  *\) *)

let remove_wc w lseq =
  match List.partition ~f:(World.eq w) lseq.worlds with
  | [], _ -> wrap_err (World.to_string w ^ " is not found.")
  | _::dups, notmatched -> wrap { lseq with worlds = List.rev_append notmatched dups }

let remove_rc rel lseq =
  match List.partition ~f:((=) rel) lseq.relations with
  | [], _ -> wrap_err ((sexp_of_world_rel rel |! Sexp.to_string_hum) ^ " is not found.")
  | _::dups, notmatched -> wrap { lseq with relations = List.rev_append notmatched dups }

let remove_tc_prop (prop, w) lseq =
  match List.partition ~f:((=) (Prop prop, w)) lseq.tcontext with
  | [], _ -> wrap_err ((Prop.Writer.to_string prop) ^ "@" ^ (World.to_string w) ^ " is not found.")
  | _::dups, notmatched -> wrap { lseq with tcontext = List.rev_append notmatched dups }

let remove_tc_mzero w lseq =
  match List.partition ~f:((=) (Mzero, w)) lseq.tcontext with
  | [], _ -> wrap_err ("Mzero@" ^ (World.to_string w) ^ " is not found.")
  | _::dups, notmatched -> wrap { lseq with tcontext = List.rev_append notmatched dups }

let remove_fc (prop, w) lseq =
  match List.partition ~f:((=) (prop, w)) lseq.fcontext with
  | [], _ -> wrap_err ((Prop.Writer.to_string prop) ^ "@" ^ (World.to_string w) ^ " is not found.")
  | _::dups, notmatched -> wrap { lseq with fcontext = List.rev_append notmatched dups }

(* let remove_wc_exn w lseq = remove_wc w lseq |! simpl_unwrap  *)
(* let remove_rc_exn ci lseq = remove_rc ci lseq |! simpl_unwrap  *)
(* let remove_tc_exn li lseq = remove_tc li lseq |! simpl_unwrap  *)
(* let remove_fc_exn ri lseq = remove_fc ri lseq |! simpl_unwrap  *)

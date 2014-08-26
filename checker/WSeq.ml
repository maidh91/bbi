(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

type state =
| Prop of Prop.t
| Mzero             (* multiplicative zero *)
  with sexp

type wstate =
| Mpair of t * t    (* multiplicative pair *)
| Apair of t * t    (* adjoint pair *)

and t = {
  world : World.t;
  tcontext : state list;   
  fcontext : Prop.t list; 
  wcontext : wstate list;
}
with sexp


(***************************************************************)
(* Main operations on a sequent *)
(***************************************************************)
(* let eq seq1 seq2 = see below *)
  
(* TODO : Refine the implemention of ''merge'' operation *)
let merge seq1 seq2 = 
  { world = seq1.world; 
    tcontext = seq1.tcontext @ seq2.tcontext; 
    fcontext = seq1.fcontext @ seq2.fcontext; 
    wcontext = seq1.wcontext @ seq2.wcontext; }
  |! wrap
  
let diff seq1 seq2 = raise NotImplemented
  
let rec apply_rename_ws rn = function
  | Mpair (wseq_1, wseq_2) -> 
    Mpair (apply_rename_s rn wseq_1, apply_rename_s rn wseq_2)
  | Apair (wseq_1, wseq_2) -> 
    Apair (apply_rename_s rn wseq_1, apply_rename_s rn wseq_2)

and apply_rename_s rn ({world = w; wcontext = wc} as wseq) =
  { wseq with world = World.rename_exn rn w; wcontext = List.map ~f:(apply_rename_ws rn) wc }

let apply_rename wrename seq = 
  try wrap (apply_rename_s wrename seq) with
  | e -> exn_wrap_err ~msg:("apply_rename failed.") e

let rec collect_world_names seq =
  let from_ctx = List.concat_map seq.wcontext ~f:(function
    | Mpair (w1,w2) 
    | Apair (w1,w2) -> 
      collect_world_names w1 
      |! List.rev_append (collect_world_names w2)) in
  seq.world :: from_ctx
  
(* World names are distinct *)
let syntactic_well_formed seq = 
  try
    collect_world_names seq
    |! List.exn_if_dup 
        ~compare:World.compare 
        ~context:"All worlds must be distinct."
        ~to_sexp:World.sexp_of_t
    |! wrap
  with
  | List.Duplicate_found (dup, msg) ->
    wrap_err ("WSeq.syntactic_well_formed failed.\n"
              ^ msg ^ " But "
              ^ (dup () |! Sexp.to_string_hum))


(***************************************************************)
(* Printer function *)
(***************************************************************)
let to_tex_tcontext_aux = function
  | Prop prop -> (Prop.Writer.to_tex prop)
  | Mzero -> ("\\multzero")
    
let to_tex_fcontext_aux prop = (Prop.Writer.to_tex prop)
  
let dummy_highlight = fun elem -> false
  
let to_tex_list_aux ?(highlight = dummy_highlight) ?(delim = ", ") printer = function
  | [] -> "\\cdot"
  | r::rlist ->
    let printer elem = if highlight elem then "\\fbox{$"^(printer elem)^"$}" else (printer elem) in
    List.fold_left ~f:(fun aux elem -> aux ^ delim ^ (printer elem))  ~init:(printer r) rlist
      
(* For now, we cannot annotate current world //w// in a SBBI sequent *)
let rec to_tex 
    ?(w_highlight = dummy_highlight) 
    ?(tc_highlight = dummy_highlight) 
    ?(fc_highlight = dummy_highlight) 
    {world=world; tcontext=t; fcontext=f; wcontext=w} = 
  let tcontext  = to_tex_list_aux ~highlight:tc_highlight to_tex_tcontext_aux t ~delim:"; " in
  let fcontext  = to_tex_list_aux ~highlight:fc_highlight to_tex_fcontext_aux f ~delim:"; " in
  let wcontext  = to_tex_list_aux (to_tex_wstate ~w_highlight:w_highlight (* ~tc_highlight:tc_highlight ~fc_highlight:fc_highlight *)) ~delim:"; " w in
  let gamma =     match t, w with
    | [], [] -> "\\cdot"
    | [], _ -> wcontext
    | _, [] -> tcontext
    | _ -> tcontext ^ "; " ^ wcontext in
  let result = "\\Jbbseqw{" ^ gamma ^ "}{" ^ fcontext ^ "}{" ^ World.to_tex world  ^ "}" in
  if w_highlight world then
    "\\fbox{$" ^ result ^ "$}"
  else
    result
      
and to_tex_wstate ?(w_highlight = dummy_highlight) ?(tc_highlight = dummy_highlight) ?(fc_highlight = dummy_highlight) = function
  | Mpair (t1, t2) -> "\\Wdown{(" 
    ^ (to_tex ~w_highlight:w_highlight ~tc_highlight:tc_highlight ~fc_highlight:fc_highlight t1) 
    ^ ")}{(" 
    ^ (to_tex ~w_highlight:w_highlight ~tc_highlight:tc_highlight ~fc_highlight:fc_highlight t2) 
    ^ ")}"
  | Apair (t1, t2) -> "\\Wup{(" 
    ^ (to_tex ~w_highlight:w_highlight ~tc_highlight:tc_highlight ~fc_highlight:fc_highlight t1) 
    ^ ")}{" 
    ^ (to_tex ~w_highlight:w_highlight ~tc_highlight:tc_highlight ~fc_highlight:fc_highlight t2) 
    ^ "}"
      
      
(***************************************************************)
(* Auxiliary operations on a sequent *)
(***************************************************************)

(* val create : World.t -> ?(tc:state list) -> ?(fc:Prop.t list) -> ?(wc:wstate list) -> t *)
let create ?(tc=[]) ?(fc=[]) ?(wc=[]) w = { world = w; tcontext = tc; fcontext = fc; wcontext = wc; }

let exists_wc_mpair (w1,w2) seq = 
  let match_mpair = function 
    | Mpair (seq1, seq2) -> World.eq w1 seq1.world && World.eq w2 seq2.world
    | _ -> false in
  if List.exists seq.wcontext ~f:match_mpair then wrap ()
  else wrap_err ("Mpair " ^ World.to_string w1 ^ World.to_string w2 ^ " is not found.")

let exists_wc_apair (w1,w2) seq = 
  let match_apair = function 
    | Apair (seq1, seq2) -> World.eq w1 seq1.world && World.eq w2 seq2.world
    | _ -> false in
  if List.exists seq.wcontext ~f:match_apair then wrap ()
  else wrap_err ("Apair " ^ World.to_string w1 ^ World.to_string w2 ^ " is not found.")

let exists_tc_prop prop seq = 
  if List.mem (Prop prop) seq.tcontext then wrap ()
  else wrap_err ((Prop.Writer.to_string prop) ^ " is not found.")

let exists_tc_mzero seq =
  if List.mem Mzero seq.tcontext then wrap ()
  else wrap_err ("Mzero is not found.")

let exists_fc prop seq = 
  if List.mem prop seq.fcontext then wrap ()
  else wrap_err ((Prop.Writer.to_string prop) ^ " is not found.")

(* 
   val add_wc_mpair : (t * t) -> t -> t result           (\* Check freshness. *\) 
   val add_wc_apair : (t * t) -> t -> t result           (\* Check freshness. *\) 
   val add_tc_prop : Prop.t -> t -> t result 
   val add_tc_mzero : t -> t result 
   val add_fc : Prop.t -> t -> t result 

   val add_tc_prop_exn : Prop.t -> t -> t
   val add_fc_exn : Prop.t -> t -> t
*)
let add_wc ws wseq = wrap { wseq with wcontext = ws :: wseq.wcontext }
let add_wc_mpair (wseq_1, wseq_2) wseq = wrap { wseq with wcontext = Mpair (wseq_1, wseq_2) :: wseq.wcontext }
let add_wc_apair (wseq_1, wseq_2) wseq = wrap { wseq with wcontext = Apair (wseq_1, wseq_2) :: wseq.wcontext }
let add_tc_prop prop wseq = wrap { wseq with tcontext = Prop prop :: wseq.tcontext }
let add_tc_mzero wseq = wrap { wseq with tcontext = Mzero :: wseq.tcontext }
let add_fc prop wseq = wrap { wseq with fcontext = prop :: wseq.fcontext }

let add_wc_exn ws wseq = add_wc ws wseq |! simpl_unwrap
let add_wc_mpair_exn (wseq_1, wseq_2) wseq = add_wc_mpair (wseq_1, wseq_2) wseq |! simpl_unwrap
let add_wc_apair_exn (wseq_1, wseq_2) wseq = add_wc_apair (wseq_1, wseq_2) wseq |! simpl_unwrap
let add_tc_prop_exn prop wseq = add_tc_prop prop wseq |! simpl_unwrap
let add_tc_mzero_exn wseq = add_tc_mzero wseq |! simpl_unwrap
let add_fc_exn prop wseq = add_fc prop wseq |! simpl_unwrap

(* 
   val remove_wc_mpair : (World.t * World.t) -> t -> t result 
   val remove_wc_apair : (World.t * World.t) -> t -> t result 
   val remove_tc_prop : Prop.t -> t -> t result 
   val remove_tc_mzero : t -> t result  (\* delete only one? *\) 
   val remove_fc : Prop.t -> t -> t result 

   val remove_tc_prop_exn : Prop.t -> t -> t
   val remove_fc_exn : Prop.t -> t -> t
*)
let rec remove_wc_mpair (w_1, w_2) wseq =
  match wseq.wcontext with
  | [] -> String.concat ["WSeq.remove_wc_mpair: there is no Mpair whose names are "; 
                         World.to_string w_1; " and "; World.to_string w_2; "."]
          |! wrap_err
  | Mpair (wseq_1, wseq_2) :: wc' ->
    if World.eq w_1 wseq_1.world && World.eq w_2 wseq_2.world then
      wrap { wseq with wcontext = wc' }
    else remove_wc_mpair (w_1, w_2) { wseq with wcontext = wc' } >> add_wc_mpair (wseq_1, wseq_2)
  | Apair (wseq_1, wseq_2) :: wc' ->
    remove_wc_mpair (w_1, w_2) { wseq with wcontext = wc' } >> add_wc_apair (wseq_1, wseq_2)

let rec remove_wc_apair (w_1, w_2) wseq =
  match wseq.wcontext with
  | [] -> String.concat ["WSeq.remove_wc_apair: there is no Apair whose names are "; 
                         World.to_string w_1; " and "; World.to_string w_2; "."]
          |! wrap_err
  | Apair (wseq_1, wseq_2) :: wc' ->
    if World.eq w_1 wseq_1.world && World.eq w_2 wseq_2.world then
      wrap { wseq with wcontext = wc' }
    else remove_wc_apair (w_1, w_2) { wseq with wcontext = wc' } >> add_wc_apair (wseq_1, wseq_2)
  | Mpair (wseq_1, wseq_2) :: wc' ->
    remove_wc_apair (w_1, w_2) { wseq with wcontext = wc' } >> add_wc_mpair (wseq_1, wseq_2)

let rec remove_tc_prop prop wseq = 
  match wseq.tcontext with
  | [] -> String.concat ["WSeq.remove_tc_prop: "; Prop.Writer.to_string prop; " is not found."] |! wrap_err 
  | Mzero :: tc' -> remove_tc_prop prop { wseq with tcontext = tc' } >> add_tc_mzero
  | (Prop prop') :: tc' ->
    if prop = prop' then 
      wrap { wseq with tcontext = tc' } 
    else remove_tc_prop prop { wseq with tcontext = tc' } >> add_tc_prop prop'

let rec remove_tc_mzero wseq = 
  match wseq.tcontext with
  | [] -> String.concat ["WSeq.remove_tc_mzero: Mzero is not found."] |! wrap_err 
  | Mzero :: tc' -> wrap { wseq with tcontext = tc' } 
  | (Prop prop') :: tc' -> remove_tc_mzero { wseq with tcontext = tc' } >> add_tc_prop prop'

let rec remove_fc prop wseq = 
  match wseq.fcontext with
  | [] -> String.concat ["WSeq.remove_fc: "; Prop.Writer.to_string prop; " is not found."] |! wrap_err 
  | prop' :: fc' ->
    if prop = prop' then 
      wrap { wseq with fcontext = fc' } 
    else remove_fc prop { wseq with fcontext = fc' } >> add_fc prop'

let remove_wc_mpair_exn prop wseq = remove_wc_mpair prop wseq |! simpl_unwrap
let remove_wc_apair_exn prop wseq = remove_wc_apair prop wseq |! simpl_unwrap
let remove_tc_prop_exn prop wseq = remove_tc_prop prop wseq |! simpl_unwrap
let remove_tc_mzero_exn wseq = remove_tc_mzero wseq |! simpl_unwrap
let remove_fc_exn prop wseq = remove_fc prop wseq |! simpl_unwrap

(* pick_wc *)
let rec pick_wc_exn f wseq =
  match wseq.wcontext with
  | [] -> exn_failure "WSeq.pick_wc: there is no world state that satisfies a given condition."
  | ws :: wc -> 
    let wseq_r = { wseq with wcontext = wc } in
    if f ws then ws, wseq_r else 
      let ws_m, wseq_mr = pick_wc_exn f wseq_r in
      ws_m, add_wc_exn ws wseq_mr

let pick_wc f wseq =
  try
    pick_wc_exn f wseq |! wrap
  with e -> exn_wrap_err ~msg:(Error.fails "pick_wc") e

let pick_wc_mpair (w1,w2) seq = 
  let get_mpair = function 
    | Mpair(wl, wr) -> World.eq w1 wl.world && World.eq w2 wr.world 
    | _ -> false in
  try
    match pick_wc get_mpair seq |! simpl_unwrap with
    | Mpair (t1,t2), remain -> wrap ((t1,t2), remain)
    | _ -> wrap_err "Impossible return value"
  with
  | e -> exn_wrap_err ~msg:("pick_wc_mpair failed") e

let pick_wc_apair (w1,w2) seq = 
  let get_apair = function 
    | Apair (wl, wr) -> World.eq w1 wl.world && World.eq w2 wr.world 
    | _ -> false in
  try
    match pick_wc get_apair seq |! simpl_unwrap with
    | Apair (t1,t2), remain -> wrap ((t1,t2), remain)
    | _ -> wrap_err "Impossible return value"
  with
  | e -> exn_wrap_err ~msg:("pick_wc_apair failed") e

(* Test eqaulity between two world sequents *)
let rec sort_s seq = { world = seq.world; 
                       tcontext = List.sort ~cmp:compare seq.tcontext; 
                       fcontext = List.sort ~cmp:compare seq.fcontext;
                       wcontext = sort_wc seq.wcontext }
and sort_ws = function
  | Mpair (seq_1, seq_2) -> Mpair (sort_s seq_1, sort_s seq_2)
  | Apair (seq_1, seq_2) -> Apair (sort_s seq_1, sort_s seq_2)

and sort_wc wc =
  let wc' = List.map ~f:sort_ws wc in
  List.sort ~cmp:compare wc'

(* 
   eq_tc : state  list -> state  list -> unit result
   eq_fc : prop   list -> prop   list -> unit result
   eq_wc : wstate list -> wstate list -> unit result
   eq_ws :           t ->           t -> unit result
 *)
let rec eq_tc tc_1 tc_2 = 
  match tc_1, tc_2 with
  | [], [] -> wrap ()
  | st_1 :: tc_1', st_2 :: tc_2' -> 
    if st_1 = st_2 then eq_tc tc_1' tc_2' else wrap_err "tc: mismatched element"
  | _  -> wrap_err "tc: mismatched length"

and eq_fc fc_1 fc_2 = 
  match fc_1, fc_2 with
  | [], [] -> wrap ()
  | prop_1 :: fc_1', prop_2 :: fc_2' -> 
    if prop_1 = prop_2 then eq_fc fc_1' fc_2' else wrap_err "fc: mismatched element"
  | _  -> wrap_err "fc: mismatched length"


and eq_wc wc_1 wc_2 = 
  match wc_1, wc_2 with
  | [], [] -> wrap ()
  | ws_1 :: wc_1', ws_2 :: wc_2' -> begin
    try
      eq_ws ws_1 ws_2 |! simpl_unwrap;
      eq_wc wc_1' wc_2' |! simpl_unwrap;
      wrap ()
    with _ -> wrap_err "wc: mismatched element"
  end
  | _ -> wrap_err "wc : mismatched length"
    
and eq_ws ws_1 ws_2 = 
  match ws_1, ws_2 with
  | Mpair (s_1, s_2), Mpair (s_1', s_2') 
  | Apair (s_1, s_2), Apair (s_1', s_2') -> begin
    try
      eq_s s_1 s_1' |! simpl_unwrap;
      eq_s s_2 s_2' |! simpl_unwrap;
      wrap ()
    with _ -> wrap_err "ws: mismatched world element"
  end
  | _ -> wrap_err "ws: mismatched element"
    
and eq_s s_1 s_2 = 
  try
    if World.eq s_1.world s_2.world then begin
      eq_tc s_1.tcontext s_2.tcontext |! simpl_unwrap;
      eq_fc s_1.fcontext s_2.fcontext |! simpl_unwrap;
      eq_wc s_1.wcontext s_2.wcontext |! simpl_unwrap;
      wrap ()
    end else wrap_err "s: mismatched name"
  with Failure msg -> wrap_err msg

let eq_opt s_1 s_2 = eq_s (sort_s s_1) (sort_s s_2)
  

let eq_naive seq1 seq2 = 
  let rec eq_aux seq1 seq2 =
    if World.eq seq1.world seq2.world then begin
      eq_list seq1.tcontext seq2.tcontext |! unwrap "tcontexts do not agree";
      eq_list seq1.fcontext seq2.fcontext |! unwrap "fcontexts do not agree";
      eq_aux_wlist seq1.wcontext seq2.wcontext []
    end
    else
      wrap_err ("World name mismatched")
  and eq_aux_wlist wctx1 wctx2 wctx2_mismatched =
    match wctx1, wctx2 with
    | (Mpair (w1, w2))::w1rest, (Mpair (w1', w2'))::w2rest 
    | (Apair (w1, w2))::w1rest, (Apair (w1', w2'))::w2rest 
      when World.eq w1.world w1'.world && World.eq w2.world w2'.world ->
      eq_aux w1 w1' |! unwrap ("Two " ^ World.to_string w1.world ^ " are not equivalent");
        eq_aux w2 w2' |! unwrap ("Two " ^ World.to_string w2.world ^ " are not equivalent");
        eq_aux_wlist w1rest (List.rev_append w2rest wctx2_mismatched) []
    (* DO NOT MATCH *)
    | _::_, w2::w2s ->
      eq_aux_wlist wctx1 w2s (w2::wctx2_mismatched)
    (* No more candidates *)
    | (Mpair (w1, w2))::_, []
    | (Apair (w1, w2))::_, [] -> wrap_err ("A wstate is not found in second sequent!:" ^ (World.to_string w1.world) ^ ", " ^ (World.to_string w2.world))
    (* wctx2 is longer *) 
    | [], (Mpair (w1, w2))::_
    | [], (Apair (w1, w2))::_ -> wrap_err ("Wcontext2 is longer:" ^ (World.to_string w1.world) ^ ", " ^ (World.to_string w2.world))
    | [], [] -> wrap ()
  in
  try eq_aux seq1 seq2 with
  | e -> exn_wrap_err ~msg:(Error.fails "WSeq.eq") e

let eq = eq_opt

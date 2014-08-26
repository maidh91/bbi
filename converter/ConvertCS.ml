(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

let mpair_with_worlds w_A w_B = function
  | WSeq.Mpair (wseq_A, wseq_B) ->
    World.eq w_A wseq_A.WSeq.world && World.eq w_B wseq_B.WSeq.world
  | _ -> false

let apair_with_worlds w_A w_B = function
  | WSeq.Apair (wseq_A, wseq_B) ->
    World.eq w_A wseq_A.WSeq.world && World.eq w_B wseq_B.WSeq.world
  | _ -> false

let wstate_with_worlds w_A w_B = function
  | WSeq.Mpair (wseq_A, wseq_B)
  | WSeq.Apair (wseq_A, wseq_B) ->
    World.eq w_A wseq_A.WSeq.world && World.eq w_B wseq_B.WSeq.world

let apair_with_sibling w_s = function
  | WSeq.Apair (wseq_s, _) ->
    World.eq w_s wseq_s.WSeq.world
  | _ -> false

let mpair_with_rchild w_r = function
  | WSeq.Mpair (_, wseq_r) ->
    World.eq w_r wseq_r.WSeq.world
  | _ -> false

let match_ws_with_worlds w_1 w_2 = function
  | WSeq.Mpair (wseq_1, wseq_2)
  | WSeq.Apair (wseq_1, wseq_2) ->
    World.eq w_1 wseq_1.WSeq.world && World.eq w_2 wseq_2.WSeq.world

let get_names = function
  | WSeq.Mpair (w_1, w_2) -> w_1.WSeq.world, w_2.WSeq.world
  | WSeq.Apair (w_1, w_2) -> w_1.WSeq.world, w_2.WSeq.world
   
let match_ws_mpair = function
  | WSeq.Mpair (wseq_A, wseq_B) -> wrap (wseq_A, wseq_B)
  | _ ->
    String.concat ["A world state of the form W, W is expected, ";
                   "but a given world state is of the form W<W>."]
    |! wrap_err

let match_ws_apair = function
  | WSeq.Apair (wseq_A, wseq_B) -> wrap (wseq_A, wseq_B)
  | _ ->
    String.concat ["A world state of the form W<W> is expected, ";
                   "but a given world state is of the form W, W."]
    |! wrap_err

let match_ws_mpair_exn ws = match_ws_mpair ws |! simpl_unwrap
let match_ws_apair_exn ws = match_ws_apair ws |! simpl_unwrap

let merge_left ~key d_1 d_2 =
  match d_1, d_2 with
  | Some v, Some _ -> Some v
  | Some v, None | None, Some v -> Some v
  | _ -> exn_failure "merge_left fail."

let merge_right ~key d_1 d_2 =
  match d_1, d_2 with
  | Some _, Some v -> Some v
  | Some v, None | None, Some v -> Some v
  | _ -> exn_failure "merge_right fail."

let merge_nodup ~key d_1 d_2 =
  match d_1, d_2 with
  | Some d, None | None, Some d -> Some d
  | _ -> exn_failure "merge_nodup fail."

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

    val backward : t -> seq -> premise result
  end

  module Build :
  sig
    type desc with sexp

    val forward : desc -> Rule.premise -> (Rule.t * Rule.seq) result
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

module Make (Spec : SPEC) =
struct

  let goal_of (_, seq, _) = seq

  let forward_exn desc prem = Spec.Build.forward desc prem |! simpl_unwrap

  let construct desc prem =
    match prem with
    | Spec.Proof.PUnit -> begin
      let rule, seq = forward_exn desc Spec.Rule.PUnit in
      (* match Spec.Rule.backward rule seq |! unwrap "construct:backward failed" with *)
      (* | Spec.Rule.PUnit -> wrap (rule, seq, prem) *)
      (* | _ -> wrap_err "construct err" *)
      wrap (rule, seq, prem)
    end
    | Spec.Proof.POne proof -> begin
      let rule, seq = forward_exn desc (Spec.Rule.POne (goal_of proof)) in
      (* match Spec.Rule.backward rule seq |! unwrap "construct:backward failed" with *)
      (* | Spec.Rule.POne _ -> wrap (rule, seq, prem) *)
      (* | _ -> wrap_err "construct err" *)
      wrap (rule, seq, prem)
    end
    | Spec.Proof.PTwo (proof_1, proof_2) -> begin
      let rule, seq = forward_exn desc (Spec.Rule.PTwo (goal_of proof_1, goal_of proof_2) )in
      (* match Spec.Rule.backward rule seq |! unwrap "construct:backward failed" with *)
      (* | Spec.Rule.PTwo _ -> wrap (rule, seq, prem) *)
      (* | _ -> wrap_err "construct err" *)
      wrap (rule, seq, prem)
    end
  let construct_exn desc prem = construct desc prem |! simpl_unwrap
  let construct_prem_exn desc prem = Spec.Proof.POne (construct_exn desc prem)
end

module SBuild = Make (SBBI)

(** Weakening *)
let rec apply_weakening_tc_aux tc sproof =
  match tc with
  | [] -> sproof
  | s :: tc' ->
    let sproof' = apply_weakening_tc_aux tc' sproof in
    SBuild.construct_exn (SBBI.Build.WeakL s) (SBBI.Proof.POne sproof')

let rec apply_weakening_fc_aux fc sproof =
  match fc with
  | [] -> sproof
  | prop :: fc' ->
    let sproof' = apply_weakening_fc_aux fc' sproof in
    SBuild.construct_exn (SBBI.Build.WeakR prop) (SBBI.Proof.POne sproof')

let rec apply_weakening_wc_aux wc sproof = 
  match wc with
  | [] -> sproof
  | ws :: wc' ->
    let sproof' = apply_weakening_wc_aux wc' sproof in
    SBuild.construct_exn (SBBI.Build.WeakW ws) (SBBI.Proof.POne sproof')

let apply_weakening_tc_exn tc sproof =
  try
    apply_weakening_tc_aux tc sproof
  with e -> exn_reraise ~msg:(Error.fails "apply_weakening_tc") e

let apply_weakening_fc_exn fc sproof =
  try
    apply_weakening_fc_aux fc sproof
  with e -> exn_reraise ~msg:(Error.fails "apply_weakening_fc") e

let apply_weakening_wc_exn wc sproof =
  try
    apply_weakening_wc_aux wc sproof
  with e -> exn_reraise ~msg:(Error.fails "apply_weakening_wc") e

(** Contraction operations *)
let rec apply_contraction_tc_aux tc sproof = 
  match tc with
  | [] -> sproof
  | s :: tc' ->
    let sproof' = apply_contraction_tc_aux tc' sproof in
    SBuild.construct_exn (SBBI.Build.ContraL s) (SBBI.Proof.POne sproof')

let rec apply_contraction_fc_aux fc sproof = 
  match fc with
  | [] -> sproof
  | prop :: fc' ->
    let sproof' = apply_contraction_fc_aux fc' sproof in
    SBuild.construct_exn (SBBI.Build.ContraR prop) (SBBI.Proof.POne sproof')

let rec apply_contraction_wc_aux rn wc sproof = 
  match wc with
  | [] -> sproof
  | ws :: wc' ->
    let sproof' = apply_contraction_wc_aux rn wc' sproof in
    SBuild.construct_exn (SBBI.Build.ContraW (get_names ws, rn)) (SBBI.Proof.POne sproof')

let apply_contraction_tc_exn tc sproof =
  try
    apply_contraction_tc_aux tc sproof
  with e -> exn_reraise ~msg:(Error.fails "apply_contraction_tc") e

let apply_contraction_fc_exn fc sproof =
  try
    apply_contraction_fc_aux fc sproof
  with e -> exn_reraise ~msg:(Error.fails "apply_contraction_fc") e

let apply_contraction_wc_exn rn wc sproof =
  try
    apply_contraction_wc_aux rn wc sproof
  with e -> exn_reraise ~msg:(Error.fails "apply_contraction_wc") e

(*
 * Instantiate existing proofs
 *)
(** Rename: Infer *)
let rec infer_rename_ws ws rn = 
  match ws with
  | WSeq.Mpair (wseq_1, wseq_2) -> 
    infer_rename_s wseq_1 rn |! infer_rename_s wseq_2 
  | WSeq.Apair (wseq_1, wseq_2) -> 
    infer_rename_s wseq_1 rn |! infer_rename_s wseq_2 

and infer_rename_s { WSeq.world = w; WSeq.wcontext = wc } rn  =
  let rn' = if Map.has_key rn w then rn else Map.add ~key:w ~data:(World.get_fresh ()) rn in
  List.fold_left ~init:rn' ~f:(fun rn ws -> infer_rename_ws ws rn) wc
    
let infer_world w rn = if Map.has_key rn w then rn else Map.add ~key:w ~data:(World.get_fresh ()) rn
    
let rec infer_rename_prem prem rn = 
  match prem with
  | SBBI.Proof.PUnit -> rn
  | SBBI.Proof.POne sproof -> infer_rename_p sproof rn
  | SBBI.Proof.PTwo (sproof_1, sproof_2) ->
    infer_rename_p sproof_1 rn |! infer_rename_p sproof_2 
    
and infer_rename_p (rule, wseq, prem) rn = infer_rename_s wseq rn |! infer_rename_rule rule |! infer_rename_prem prem

and infer_rename_split { SBBI.Rule.selected_wc = wc } rn = 
    List.fold_left ~init:rn ~f:(fun rn (w_1, w_2) -> infer_world w_1 rn |! infer_world w_2) wc
    
and infer_rename_rule rule rn = 
  match rule with
  | SBBI.Rule.Init -> rn
  | SBBI.Rule.TopL -> rn
  | SBBI.Rule.TopR -> rn
  | SBBI.Rule.BotL -> rn
  | SBBI.Rule.BotR -> rn
  | SBBI.Rule.NegL _ -> rn
  | SBBI.Rule.NegR _ -> rn
  | SBBI.Rule.AndL _ -> rn
  | SBBI.Rule.AndR (_, sp) -> infer_rename_split sp rn
  | SBBI.Rule.OrL (_, sp) -> infer_rename_split sp rn
  | SBBI.Rule.OrR _ -> rn
  | SBBI.Rule.ImplyL (_, sp) -> infer_rename_split sp rn
  | SBBI.Rule.ImplyR _ -> rn
  | SBBI.Rule.UnitL _ -> rn
  | SBBI.Rule.UnitR _ -> rn
  | SBBI.Rule.StarL (_, (w_A, w_B)) ->
    infer_world w_A rn |! infer_world w_B
  | SBBI.Rule.StarR -> rn
  | SBBI.Rule.WandL -> rn
  | SBBI.Rule.WandR (_, (w_A, w_B)) ->
    infer_world w_A rn |! infer_world w_B
  | SBBI.Rule.TC (w_1, w_2) -> 
    infer_world w_1 rn |! infer_world w_2
  | SBBI.Rule.TP (w_1, w_2) -> 
    infer_world w_1 rn |! infer_world w_2
  | SBBI.Rule.WeakL _ -> rn
  | SBBI.Rule.WeakR _ -> rn
  | SBBI.Rule.WeakW (w_1, w_2) -> 
    infer_world w_1 rn |! infer_world w_2
  | SBBI.Rule.ContraL _ -> rn
  | SBBI.Rule.ContraR _ -> rn
  | SBBI.Rule.ContraW (w_1, w_2, rn_new) ->
    Map.fold ~f:(fun ~key:w_s ~data:w_t rn_acc -> infer_world w_s rn_acc |! infer_world w_t) ~init:rn rn_new
    |! infer_world w_1 
    |! infer_world w_2
  | SBBI.Rule.Comm (w_1, w_2) ->
    infer_world w_1 rn |! infer_world w_2
  | SBBI.Rule.Assoc ((w_1n2, w_3), w_new) ->
    infer_world w_1n2 rn |! infer_world w_3 |! infer_world w_new
  | SBBI.Rule.ZeroU (sp, (w_l, w_r)) ->
    infer_rename_split sp rn
    |! infer_world w_l 
    |! infer_world w_r
  | SBBI.Rule.ZeroD (w_l, w_r) ->
    infer_world w_l rn |! infer_world w_r
              
(** Rename: Apply *)
let rec apply_rename_ws rn = function
  | WSeq.Mpair (wseq_1, wseq_2) -> 
    WSeq.Mpair (apply_rename_s rn wseq_1, apply_rename_s rn wseq_2)
  | WSeq.Apair (wseq_1, wseq_2) -> 
    WSeq.Apair (apply_rename_s rn wseq_1, apply_rename_s rn wseq_2)

and apply_rename_s rn ({WSeq.world = w; WSeq.wcontext = wc} as wseq) =
  { wseq with WSeq.world = World.rename_exn rn w; WSeq.wcontext = List.map ~f:(apply_rename_ws rn) wc }

let rec apply_rename_prem rn = function
  | SBBI.Proof.PUnit -> SBBI.Proof.PUnit
  | SBBI.Proof.POne sproof -> 
    SBBI.Proof.POne (apply_rename_p rn sproof)
  | SBBI.Proof.PTwo (sproof_1, sproof_2) -> 
    SBBI.Proof.PTwo (apply_rename_p rn sproof_1, apply_rename_p rn sproof_2)

and apply_rename_p rn (rule, wseq, prem) = apply_rename_rule rn rule, apply_rename_s rn wseq, apply_rename_prem rn prem

and apply_rename_split rn ({ SBBI.Rule.selected_wc = wc } as sp) = 
    { sp with SBBI.Rule.selected_wc = List.map ~f:(fun (w_1, w_2) -> World.rename_exn rn w_1, World.rename_exn rn w_2) wc }

and apply_rename_rule rn rule = 
  match rule with
  | SBBI.Rule.Init -> rule
  | SBBI.Rule.TopL -> rule
  | SBBI.Rule.TopR -> rule
  | SBBI.Rule.BotL -> rule
  | SBBI.Rule.BotR -> rule
  | SBBI.Rule.NegL _ -> rule
  | SBBI.Rule.NegR _ -> rule
  | SBBI.Rule.AndL _ -> rule
  | SBBI.Rule.AndR (prop, sp) -> SBBI.Rule.AndR (prop, apply_rename_split rn sp)
  | SBBI.Rule.OrL (prop, sp) -> SBBI.Rule.OrL (prop, apply_rename_split rn sp)
  | SBBI.Rule.OrR _ -> rule
  | SBBI.Rule.ImplyL (prop, sp) -> SBBI.Rule.ImplyL (prop, apply_rename_split rn sp)
  | SBBI.Rule.ImplyR _ -> rule
  | SBBI.Rule.UnitL _ -> rule
  | SBBI.Rule.UnitR _ -> rule
  | SBBI.Rule.StarL (prop, (w_A, w_B)) ->
    SBBI.Rule.StarL (prop, (World.rename_exn rn w_A, World.rename_exn rn w_B))
  | SBBI.Rule.StarR -> rule
  | SBBI.Rule.WandL -> rule
  | SBBI.Rule.WandR (prop, (w_A, w_B)) ->
    SBBI.Rule.WandR (prop, (World.rename_exn rn w_A, World.rename_exn rn w_B))
  | SBBI.Rule.TC (w_1, w_2) -> 
    SBBI.Rule.TC (World.rename_exn rn w_1, World.rename_exn rn w_2)
  | SBBI.Rule.TP (w_1, w_2) -> 
    SBBI.Rule.TP (World.rename_exn rn w_1, World.rename_exn rn w_2)
  | SBBI.Rule.WeakL _ -> rule
  | SBBI.Rule.WeakR _ -> rule
  | SBBI.Rule.WeakW (w_1, w_2) -> 
    SBBI.Rule.WeakW (World.rename_exn rn w_1, World.rename_exn rn w_2)
  | SBBI.Rule.ContraL _ -> rule
  | SBBI.Rule.ContraR _ -> rule
  | SBBI.Rule.ContraW (w_1, w_2, rn_new) -> begin
    try
      let rn_new' = 
        Map.fold ~f:(fun ~key:w_s ~data:w_t rn_acc -> Map.add ~key:(World.rename_exn rn w_s) ~data:(World.rename_exn rn w_t) rn_acc)
          ~init:Map.empty rn_new in
      SBBI.Rule.ContraW (World.rename_exn rn w_1, World.rename_exn rn w_2, rn_new')
    with e -> exn_reraise ~msg:(Error.fails "apply_rename_p_contra_w") e
  end
  | SBBI.Rule.Comm (w_1, w_2) -> SBBI.Rule.Comm (World.rename_exn rn w_1, World.rename_exn rn w_2)
  | SBBI.Rule.Assoc ((w_1n2, w_3), w_new) -> 
    SBBI.Rule.Assoc ((World.rename_exn rn w_1n2, World.rename_exn rn w_3), World.rename_exn rn w_new)
  | SBBI.Rule.ZeroU (sp, (w_l, w_r)) ->
    SBBI.Rule.ZeroU (apply_rename_split rn sp, (World.rename_exn rn w_l, World.rename_exn rn w_r))
  | SBBI.Rule.ZeroD (w_l, w_r) ->
    SBBI.Rule.ZeroD (World.rename_exn rn w_l, World.rename_exn rn w_r)      
                                                                
let infer_and_apply_rename_ws rn ws =
  let rn = infer_rename_ws ws rn in
  rn, apply_rename_ws rn ws

(* Calculate world name mapping from two sequents with 
   the same structure. *)
let eq_list_bool l1 l2 =
  try 
    eq_list l1 l2 |! simpl_unwrap; true
  with _ -> false

module type INFER_RENAME =
sig
  val compute : WSeq.t -> (World.t * World.t) -> (World.t * World.t) -> World.rename option 
end

module NaiveInferRename : INFER_RENAME =
struct
  let rec calc_rename_contraw_ws wseq1 wseq2 = 
    if eq_list_bool wseq1.WSeq.tcontext wseq2.WSeq.tcontext
      && eq_list_bool wseq1.WSeq.fcontext wseq2.WSeq.fcontext then
      match calc_rename_contraw_wc wseq1.WSeq.wcontext wseq2.WSeq.wcontext [] with
      | Some rn -> Some (Map.add ~key:wseq1.WSeq.world ~data:wseq2.WSeq.world rn)
      | None -> None
    else
      None

  and calc_rename_contraw_wc wc1 wc2 wc2_mismatched =
    match wc1, wc2 with 
    | (WSeq.Mpair (ws1, ws2))::wc1rest, (WSeq.Mpair (ws1', ws2') as ws)::wc2rest 
    | (WSeq.Apair (ws1, ws2))::wc1rest, (WSeq.Apair (ws1', ws2') as ws)::wc2rest -> begin
      try
        let rn1 = calc_rename_contraw_ws ws1 ws1' |! Option.value_exn in
        let rn2 = calc_rename_contraw_ws ws2 ws2' |! Option.value_exn in
        let rnr = calc_rename_contraw_wc wc1rest (List.rev_append wc2rest wc2_mismatched) [] |! Option.value_exn in
        let rn_merged = Map.merge ~f:merge_nodup rn1 rn2 
                        |! Map.merge ~f:merge_nodup rnr in
        Some rn_merged
      with
      | _ -> 
        calc_rename_contraw_wc wc1 wc2rest (ws::wc2_mismatched)
    end
    | _::_, ws::wc2rest ->
      calc_rename_contraw_wc wc1 wc2rest (ws::wc2_mismatched)
    | [], [] -> Some Map.empty
    | _ -> None

  let compute wseq (w1,w2) (w1', w2') = 
    let ws_1, _ = WSeq.pick_wc_exn (wstate_with_worlds w1 w2) wseq in 
    let ws_2, _ = WSeq.pick_wc_exn (wstate_with_worlds w1' w2') wseq in 
    calc_rename_contraw_wc [ws_1] [ws_2] [] 
end


(* Another implementation: maybe linear complexity *)
module ParjongInferRename : INFER_RENAME
  =
struct
  let state_to_string = function
    | WSeq.Mzero -> "Mzero"
    | WSeq.Prop p -> Prop.Writer.to_string p

  (* 
     hash_w  : WSeq.t           -> (World.t, int) Map.t
     hash_wc : WSeq.wstate list -> int * (World.t, int) Map.t
  *)
  let rec hash_w { WSeq.world = w; WSeq.tcontext = tc; WSeq.fcontext = fc; WSeq.wcontext = wc } = 
    let tc_id = List.fold_left ~init:0 ~f:(fun acc st -> acc + (state_to_string st |! Hashtbl.hash)) tc in
    let fc_id = List.fold_left ~init:0 ~f:(fun acc p  -> acc + (Prop.Writer.to_string p |! Hashtbl.hash)) fc in
    let wc_id, id_map = hash_wc wc in
    Map.add ~key:w ~data:(tc_id + fc_id + wc_id) id_map

  and hash_wc = function 
    | [] -> 1, Map.empty
    | WSeq.Mpair (w_l, w_r) :: wc -> 
      let n, rn = hash_wc wc in
      let rn' = Map.merge ~f:merge_nodup (hash_w w_l) (hash_w w_r)
                |! Map.merge ~f:merge_nodup rn in             
      2 + n, rn'
    | WSeq.Apair (w_s, w_p) :: wc ->
      let n, rn = hash_wc wc in
      let rn' = Map.merge ~f:merge_nodup (hash_w w_s) (hash_w w_p)
                |! Map.merge ~f:merge_nodup rn in
      3 + n, rn'

  let get_hash_ws h = function
    | WSeq.Mpair (w1, w2) | WSeq.Apair (w1, w2) -> 
      Map.find_exn h w1.WSeq.world, Map.find_exn h w2.WSeq.world

  let rec compute_rename_w h wseq_1 wseq_2 = 
    let { WSeq.world = w_1; WSeq.tcontext = tc_1; WSeq.fcontext = fc_1; WSeq.wcontext = wc_1 } = wseq_1 in
    let { WSeq.world = w_2; WSeq.tcontext = tc_2; WSeq.fcontext = fc_2; WSeq.wcontext = wc_2 } = wseq_2 in
    if eq_list_bool tc_1 tc_2 && eq_list_bool fc_1 fc_2 then
      match compute_rename_wc h wc_1 wc_2 with
      | Some rn -> Some (Map.add ~key:w_1 ~data:w_2 rn)
      | None    -> None      
    else None

  and compute_rename_wc_aux h ws wc acc =
    match ws, wc with 
    | WSeq.Mpair (w1, w2), (WSeq.Mpair (w1', w2') as ws') :: wc_rest 
    | WSeq.Apair (w1, w2), (WSeq.Apair (w1', w2') as ws') :: wc_rest -> begin
      try
        let rn_1 = compute_rename_w h w1 w1' |! Option.value_exn in
        let rn_2 = compute_rename_w h w2 w2' |! Option.value_exn in
        Some (Map.merge ~f:merge_nodup rn_1 rn_2, wc_rest @ acc)
      with
      | _ -> compute_rename_wc_aux h ws wc_rest (ws' :: acc)
    end
    | _, ws' :: wc_rest -> compute_rename_wc_aux h ws wc_rest (ws' :: acc)
    | _, []             -> None

  and compute_rename_wc h wc1 wc2 =
    match wc1 with
    | [] -> begin
      match wc2 with
      | [] -> Some Map.empty
      | _  -> None
    end
    | ws_1 :: wc1_r -> begin
      try
        let wc2_s, wc2_r = List.partition ~f:(fun ws_2 -> (get_hash_ws h ws_1) = (get_hash_ws h ws_2)) wc2 in
        let rn_cur, wc2_sr = compute_rename_wc_aux h ws_1 wc2_s []
                             |! Option.value_exn in
        let rn_rest        = compute_rename_wc h wc1_r (wc2_sr @ wc2_r)
                             |! Option.value_exn in
        Some (Map.merge ~f:merge_nodup rn_cur rn_rest)
      with _ -> None
    end

  let compute wseq (w1, w2) (w1', w2') =     
    let ws1, _ = WSeq.pick_wc_exn (wstate_with_worlds w1 w2) wseq in
    let ws2, _ = WSeq.pick_wc_exn (wstate_with_worlds w1' w2') wseq in
    let _, h1 = hash_wc [ws1] in
    let _, h2 = hash_wc [ws2] in
    compute_rename_wc (Map.merge ~f:merge_nodup h1 h2) [ws1] [ws2]
end

module BaramseoInferRename : INFER_RENAME =
struct
  let state_to_string = function
    | WSeq.Mzero -> "Mzero"
    | WSeq.Prop p -> Prop.Writer.to_string p

  (* val serialize_w : WSeq.t -> int * ((World.t * int) list) *)
  (* [serialize_w wseq] returns a hash value of [wseq] and assoc list of *)
  (*    world and corresponding hash values *)
  let rec serialize_w wseq =
    let cmp_hash ((a1,a2),_) ((b1,b2),_) =
      if a1 = b1 then a2 - b2
      else a1 - b1 in
    let w_hash, maps = List.map wseq.WSeq.wcontext ~f:serialize_ws
                       |! List.sort ~cmp:cmp_hash
                       |! List.split
                       |! (fun (hash_list, map_list) ->
                         Hashtbl.hash hash_list,
                         List.flatten map_list)
    in
    let t_hash = List.map wseq.WSeq.tcontext ~f:state_to_string
                 |! List.sort ~cmp:Core.Core_string.compare
                 |! Hashtbl.hash in
    let f_hash = List.map wseq.WSeq.fcontext ~f:Prop.Writer.to_string
                 |! List.sort ~cmp:Core.Core_string.compare
                 |! Hashtbl.hash in
    let hash = Hashtbl.hash [t_hash; f_hash; w_hash] in
    hash, (wseq.WSeq.world, hash)::maps

  (* val serialize_ws : WSeq.wstate -> (int, int) * (World.t * int) list *)
  and serialize_ws = function
    | WSeq.Mpair (w1, w2)
    | WSeq.Apair (w1, w2) ->
      let w1, w1s = serialize_w w1 in
      let w2, w2s = serialize_w w2 in
      (w1,w2), List.rev_append w1s w2s

  and compute wseq (w1,w2) (w1', w2') =
    let ws_1, _ = WSeq.pick_wc_exn (wstate_with_worlds w1 w2) wseq in
    let ws_2, _ = WSeq.pick_wc_exn (wstate_with_worlds w1' w2') wseq in
    let ws_1_hash, ws_1_map = serialize_ws ws_1 in
    let ws_2_hash, ws_2_map = serialize_ws ws_2 in
    if ws_1_hash <> ws_2_hash then
      failwith "calc_rename_contraw: hash values disagree."
    else
      let collision_1 = List.map ws_1_map ~f:snd
                        |! List.contains_dup in
      let collision_2 = List.map ws_2_map ~f:snd
                        |! List.contains_dup in
      if collision_1 || collision_2 then begin
        (* Printf.fprintf stderr "calc_rename_contraw: hash value \ collision occured\n"; *)
        NaiveInferRename.compute wseq (w1,w2) (w1',w2')
      end
      else
        let w_1 = List.sort ws_1_map ~cmp:(fun (_,h1) (_,h2) -> h1-h2)
                  |! List.map ~f:fst in
        let w_2 = List.sort ws_2_map ~cmp:(fun (_,h1) (_,h2) -> h1-h2)
                  |! List.map ~f:fst in
        Some (List.combine_exn w_1 w_2 |! Map.of_alist_exn)
end

module InferRename : INFER_RENAME = ParjongInferRename


(** Convert a CS_BBI proof into a S_BBI proof *)
let rec convert_aux (crule, wseq, cprem) =
  match crule with
  | CSBBI.Rule.Init prop -> begin
    try
      let { WSeq.world = w; WSeq.tcontext = tc; WSeq.fcontext = fc; WSeq.wcontext = wc } = 
        WSeq.remove_tc_prop_exn prop wseq |! WSeq.remove_fc_exn prop in
      SBuild.construct_exn (SBBI.Build.Init (w, prop)) (SBBI.Proof.PUnit)
      |! apply_weakening_tc_exn tc 
      |! apply_weakening_fc_exn fc 
      |! apply_weakening_wc_exn wc 
    with e -> exn_reraise ~msg:(Error.fails "convert_init") e
  end
  | CSBBI.Rule.TopR -> begin
    try
      let { WSeq.world = w; WSeq.tcontext = tc; WSeq.fcontext = fc; WSeq.wcontext = wc } = 
        WSeq.remove_fc_exn Prop.Top wseq in
      SBuild.construct_exn (SBBI.Build.TopR w) (SBBI.Proof.PUnit)
      |! apply_weakening_tc_exn tc 
      |! apply_weakening_fc_exn fc 
      |! apply_weakening_wc_exn wc 
    with e -> exn_reraise ~msg:(Error.fails "convert_top_right") e
  end
  | CSBBI.Rule.BotL -> begin
    try
      let { WSeq.world = w; WSeq.tcontext = tc; WSeq.fcontext = fc; WSeq.wcontext = wc } = 
        WSeq.remove_tc_prop_exn Prop.Bot wseq in
      SBuild.construct_exn (SBBI.Build.BotL w) (SBBI.Proof.PUnit)
      |! apply_weakening_tc_exn tc 
      |! apply_weakening_fc_exn fc 
      |! apply_weakening_wc_exn wc 
    with e -> exn_reraise ~msg:(Error.fails "convert_bot_left") e
  end
  | CSBBI.Rule.NegL prop -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let sproof = convert_aux cproof in
      SBuild.construct_exn (SBBI.Build.NegL prop) (SBBI.Proof.POne sproof)
    with e -> exn_reraise ~msg:(Error.fails "convert_neg_left") e
  end
  | CSBBI.Rule.NegR prop -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let sproof = convert_aux cproof in
      SBuild.construct_exn (SBBI.Build.NegR prop) (SBBI.Proof.POne sproof)
    with e -> exn_reraise ~msg:(Error.fails "convert_neg_right") e
  end
  | CSBBI.Rule.AndL prop -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let sproof = convert_aux cproof in
      SBuild.construct_exn (SBBI.Build.AndL prop) (SBBI.Proof.POne sproof)
    with e -> exn_reraise ~msg:(Error.fails "convert_and_left") e
  end
  | CSBBI.Rule.AndR prop -> begin
    try
      let prop_A, _ = Prop.match_prop_and_exn prop in
      let cproof_A, cproof_B = CSBBI.Proof.match_prem_two_exn cprem in
      let _, ({ WSeq.world = w_A } as wseq_A), _ as sproof_A = convert_aux cproof_A in
      let _, { WSeq.world = w_B }, _ as sproof_B = convert_aux cproof_B in
      (* Renaming *)
      let rn = Map.of_alist_exn [w_B, w_A] |! infer_rename_p sproof_B  in
      let sproof_B' = apply_rename_p rn sproof_B in
      (* Contraction *)
      let { WSeq.tcontext = tc; WSeq.fcontext = fc; WSeq.wcontext = wc; } = WSeq.remove_fc_exn prop_A wseq_A in
      SBuild.construct_exn (SBBI.Build.AndR prop) (SBBI.Proof.PTwo (sproof_A, sproof_B'))
      |! apply_contraction_tc_exn tc
      |! apply_contraction_fc_exn fc
      |! apply_contraction_wc_exn rn wc
    with e -> exn_reraise ~msg:(Error.fails "convert_and_right") e
  end
  | CSBBI.Rule.OrL prop -> begin
    try
      let prop_A, _ = Prop.match_prop_or_exn prop in
      let cproof_A, cproof_B = CSBBI.Proof.match_prem_two_exn cprem in
      let _, ({ WSeq.world = w_A } as wseq_A), _ as sproof_A = convert_aux cproof_A in
      let _, { WSeq.world = w_B }, _ as sproof_B = convert_aux cproof_B in
      (* Renaming *)
      let rn = Map.of_alist_exn [w_B, w_A] |! infer_rename_p sproof_B  in
      let sproof_B' = apply_rename_p rn sproof_B in
      (* Contraction *)
      let { WSeq.tcontext = tc; WSeq.fcontext = fc; WSeq.wcontext = wc; } = WSeq.remove_tc_prop_exn prop_A wseq_A in
      SBuild.construct_exn (SBBI.Build.OrL prop) (SBBI.Proof.PTwo (sproof_A, sproof_B'))
      |! apply_contraction_tc_exn tc
      |! apply_contraction_fc_exn fc
      |! apply_contraction_wc_exn rn wc
    with e -> exn_reraise ~msg:(Error.fails "convert_or_left") e
  end
  | CSBBI.Rule.OrR prop -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let sproof = convert_aux cproof in
      SBuild.construct_exn (SBBI.Build.OrR prop) (SBBI.Proof.POne sproof)
    with e -> exn_reraise ~msg:(Error.fails "convert_or_right") e
  end
  | CSBBI.Rule.ImplyL prop -> begin
    try
      let prop_A, _ = Prop.match_prop_imply_exn prop in
      let cproof_A, cproof_B = CSBBI.Proof.match_prem_two_exn cprem in
      let _, ({ WSeq.world = w_A } as wseq_A), _ as sproof_A = convert_aux cproof_A in
      let _, { WSeq.world = w_B }, _ as sproof_B = convert_aux cproof_B in
      (* Renaming *)
      let rn = Map.of_alist_exn [w_B, w_A] |! infer_rename_p sproof_B  in
      let sproof_B' = apply_rename_p rn sproof_B in
      (* Contraction *)
      let { WSeq.tcontext = tc; WSeq.fcontext = fc; WSeq.wcontext = wc; } = WSeq.remove_fc_exn prop_A wseq_A in
      SBuild.construct_exn (SBBI.Build.ImplyL prop) (SBBI.Proof.PTwo (sproof_A, sproof_B'))
      |! apply_contraction_tc_exn tc
      |! apply_contraction_fc_exn fc
      |! apply_contraction_wc_exn rn wc
    with e -> exn_reraise ~msg:(Error.fails "convert_imply_left") e
  end
  | CSBBI.Rule.ImplyR prop -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let sproof = convert_aux cproof in
      SBuild.construct_exn (SBBI.Build.ImplyR prop) (SBBI.Proof.POne sproof)
    with e -> exn_reraise ~msg:(Error.fails "convert_imply_right") e
  end
  | CSBBI.Rule.UnitL -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let sproof = convert_aux cproof in
      SBuild.construct_exn SBBI.Build.UnitL (SBBI.Proof.POne sproof)
    with e -> exn_reraise ~msg:(Error.fails "convert_unit_left") e
  end
  | CSBBI.Rule.UnitR -> begin
    try
      let { WSeq.world = w; WSeq.tcontext = tc; WSeq.fcontext = fc; WSeq.wcontext = wc } = 
        WSeq.remove_tc_mzero_exn wseq |! WSeq.remove_fc_exn Prop.Unit in
      SBuild.construct_exn (SBBI.Build.UnitR w) SBBI.Proof.PUnit
      |! apply_weakening_tc_exn tc
      |! apply_weakening_wc_exn wc 
      |! apply_weakening_fc_exn fc 
    with e -> exn_reraise ~msg:(Error.fails "convert_unit_right") e
  end
  | CSBBI.Rule.StarL (prop, (w_A, w_B))-> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let sproof = convert_aux cproof in
      SBuild.construct_exn (SBBI.Build.StarL (prop, (w_A, w_B))) (SBBI.Proof.POne sproof)
    with e -> exn_reraise ~msg:(Error.fails "convert_star_left") e
  end
  | CSBBI.Rule.StarR ((w_1, w_2), prop) -> begin
    try
      let cproof_A, cproof_B = CSBBI.Proof.match_prem_two_exn cprem in
      let (wseq_1, _), _ = CSBBI.Proof.seq_of cproof_B
                           |! WSeq.pick_wc (mpair_with_worlds w_1 w_2)
                           |! unwrap "Can't compute wseq_1."
                           |! Tuple.T2.map1 ~f:match_ws_mpair_exn in
      let (_, wseq_2), wseq_p = CSBBI.Proof.seq_of cproof_A
                                |! WSeq.pick_wc (mpair_with_worlds w_1 w_2)
                                |! unwrap "Can't compute wseq_2."
                                |! Tuple.T2.map1 ~f:match_ws_mpair_exn in
      let { WSeq.world = w_p } = wseq_p in
      let rn_s2 = infer_rename_ws (WSeq.Apair (wseq_1, wseq_p)) Map.empty in
      let ws_2 = apply_rename_ws rn_s2 (WSeq.Apair (wseq_1, wseq_p)) in
      (* Construct the left premise *)
      let sproof_A = convert_aux cproof_A in
      let sproof_A' =
        SBuild.construct_prem_exn (SBBI.Build.Comm (w_2, w_1)) (SBBI.Proof.POne sproof_A)
        |! SBuild.construct_exn (SBBI.Build.TP (w_1, w_p))
        |! apply_weakening_wc_exn [ws_2]
        |! (fun sproof -> SBuild.construct_prem_exn (SBBI.Build.TC (w_2, w_1)) (SBBI.Proof.POne sproof))
        |! SBuild.construct_prem_exn (SBBI.Build.Comm (w_1, w_2))
        |! SBuild.construct_prem_exn (SBBI.Build.TP (w_2, w_p)) 
        |! SBBI.Proof.match_prem_one_exn in
      (* Construct the right premise *)
      let sproof_B = convert_aux cproof_B in
      let rn_B = infer_rename_p sproof_B Map.empty in
      let sproof_B' =
        apply_rename_p rn_B sproof_B
        |! (fun sproof ->
          SBuild.construct_exn (SBBI.Build.Comm (World.rename_exn rn_B w_2, World.rename_exn rn_B w_1)) (SBBI.Proof.POne sproof))
        |! (fun sproof ->
          SBuild.construct_exn (SBBI.Build.TP (World.rename_exn rn_B w_1, World.rename_exn rn_B w_p)) (SBBI.Proof.POne sproof)) in
      (* Construct the conclusion *)
      let w_new = World.get_fresh () in
      let wseq_r = WSeq.remove_fc prop wseq_p |! unwrap "Can't remove A * B." in
      let rn_r' = infer_rename_s wseq_r Map.empty in
      let rn_r = Map.remove rn_r' w_p in
      let { WSeq.tcontext = tc; WSeq.fcontext = fc; WSeq.wcontext = wc } = apply_rename_s rn_r' wseq_r in
      let new_rn_s2 =
        List.map ~f:(fun w -> World.rename_exn rn_s2 w, World.rename_exn rn_B w) (Map.keys rn_s2) |! Map.of_alist_exn in
      let rn_s1 = Map.merge ~f:merge_nodup (Map.merge ~f:merge_left (Map.add ~key:w_p ~data:w_new rn_r) rn_B) new_rn_s2 in
      SBuild.construct_exn (SBBI.Build.StarR (w_new, prop)) (SBBI.Proof.PTwo (sproof_A', sproof_B'))
      |! apply_weakening_tc_exn tc 
      |! apply_weakening_fc_exn fc
      |! apply_weakening_wc_exn wc
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (World.rename_exn rn_B w_2, w_new)) (SBBI.Proof.POne sproof)) 
      (*  *)
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.ContraW ((w_2, w_p), rn_s1)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (w_1, w_2)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_2, w_1)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_1, w_p)) (SBBI.Proof.POne sproof)) 
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.ContraW ((w_1, w_p), rn_s2)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (w_2, w_1)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_1, w_2)) (SBBI.Proof.POne sproof))
    with e -> exn_reraise ~msg:(Error.fails "convert_star_right") e
  end
  | CSBBI.Rule.WandL ((w_1, w_2), prop) -> begin
    try
      let cproof_A, cproof_B = CSBBI.Proof.match_prem_two_exn cprem in
      let (_, wseq_2), wseq_p = CSBBI.Proof.seq_of cproof_A
                                |! WSeq.pick_wc (apair_with_worlds w_1 w_2)
                                |! unwrap "Can't compute wseq_2."
                                |! Tuple.T2.map1 ~f:match_ws_apair_exn in
      let { WSeq.world = w_p } = wseq_p in
      (* Construct the left premise *)
      let sproof_A = 
        convert_aux cproof_A
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (w_p, w_1)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_1, w_p)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_p, w_2)) (SBBI.Proof.POne sproof)) in
      (* Construct the right premise *)
      let sproof_B_raw = convert_aux cproof_B in
      (* -- Compute RN for the right proof *)
      let rn_B = infer_rename_p sproof_B_raw Map.empty in
      let rn_B_w_1 = World.rename_exn rn_B w_1 in
      let rn_B_w_2 = World.rename_exn rn_B w_2 in
      let rn_B_w_p = World.rename_exn rn_B w_p in
      (* -- Compute WS for the right proof *)
      let ws1_raw = WSeq.Apair (wseq_p, wseq_2) in
      let rn_ws1 = infer_rename_ws ws1_raw Map.empty in
      let ws_1 = apply_rename_ws rn_ws1 ws1_raw in
      (* -- Real Construction! *)
      let sproof_B = 
        apply_rename_p rn_B sproof_B_raw
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (rn_B_w_p, rn_B_w_1)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (rn_B_w_1, rn_B_w_p)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (rn_B_w_p, rn_B_w_2)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.WeakW ws_1) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (rn_B_w_1, rn_B_w_p)) (SBBI.Proof.POne sproof)) 
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (rn_B_w_p, rn_B_w_1)) (SBBI.Proof.POne sproof)) in
      (* Apply WandL! & Weakening *)
      let new_w_p = World.get_fresh () in
      let wseq_W = wseq_p |! WSeq.remove_tc_prop_exn prop in
      let rn_W_raw = infer_rename_s wseq_W Map.empty in
      let rn_W = Map.remove rn_W_raw w_p in
      let { WSeq.tcontext = tc_W; WSeq.fcontext = fc_W; WSeq.wcontext = wc_W } = apply_rename_s rn_W_raw wseq_W in
      let new_rn_W =
        List.map ~f:(fun w -> World.rename_exn rn_W w, World.rename_exn rn_B w) (Map.keys rn_W) |! Map.of_alist_exn 
        |! Map.add ~key:new_w_p ~data:(World.rename_exn rn_B w_p) in
      let rn_ws2 = Map.merge ~f:merge_nodup (Map.merge ~f:merge_left rn_ws1 rn_B) new_rn_W in
      let rn_ws1 = Map.merge ~f:merge_left (Map.add ~key:w_p ~data:new_w_p rn_W) rn_B in
      SBuild.construct_exn (SBBI.Build.WandL (new_w_p, prop)) (SBBI.Proof.PTwo (sproof_A, sproof_B))
      |! apply_weakening_tc_exn tc_W
      |! apply_weakening_fc_exn fc_W
      |! apply_weakening_wc_exn wc_W
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (new_w_p, w_1)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.ContraW ((new_w_p, w_1), rn_ws2)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_1, new_w_p)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (new_w_p, rn_B_w_2)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.ContraW ((w_p, w_2), rn_ws1)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (w_1, w_p)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_p, w_1)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_1, w_2)) (SBBI.Proof.POne sproof))
    with e -> exn_reraise ~msg:(Error.fails "convert_wand_left") e
  end
  | CSBBI.Rule.WandR (prop, (w_A, w_B))-> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let sproof = convert_aux cproof in
      SBuild.construct_exn (SBBI.Build.WandR (prop, (w_A, w_B))) (SBBI.Proof.POne sproof)
    with e -> exn_reraise ~msg:(Error.fails "convert_wand_right") e
  end
  | CSBBI.Rule.TC (w_c1, w_c2) -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let sproof = convert_aux cproof in
      SBuild.construct_exn (SBBI.Build.TC (w_c1, w_c2)) (SBBI.Proof.POne sproof)
    with e -> exn_reraise ~msg:(Error.fails "convert_tc") e
  end
  | CSBBI.Rule.TP (w_s, w_p) -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let sproof = convert_aux cproof in
      SBuild.construct_exn (SBBI.Build.TP (w_s, w_p)) (SBBI.Proof.POne sproof)
    with e -> exn_reraise ~msg:(Error.fails "convert_tp") e
  end
  | CSBBI.Rule.Comm (w_l, w_r) -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let sproof = convert_aux cproof in
      SBuild.construct_exn (SBBI.Build.Comm (w_l, w_r)) (SBBI.Proof.POne sproof)
    with e -> exn_reraise ~msg:(Error.fails "convert_comm") e
  end
  | CSBBI.Rule.ZeroU (_, (rn, w_e)) -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let _, wseq, _ as sproof = convert_aux cproof in
      let { WSeq.world = w_p } = wseq in
      let _, { WSeq.tcontext = tc; WSeq.fcontext = fc; WSeq.wcontext = wc } = 
        WSeq.pick_wc_exn (mpair_with_worlds (World.rename_exn rn w_p) w_e) wseq in
      SBuild.construct_exn (SBBI.Build.ZeroU (World.rename_exn rn w_p, w_e)) (SBBI.Proof.POne sproof)
      |! apply_contraction_tc_exn tc
      |! apply_contraction_fc_exn fc
      |! apply_contraction_wc_exn rn wc
    with e -> exn_reraise ~msg:(Error.fails "convert_zero_up") e
  end
  | CSBBI.Rule.ZeroD ((w_l, w_r), rn_new) -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let _, wseq, _ as sproof = convert_aux cproof in
      let { WSeq.world = w_p } = wseq in
      let (wseq_c1, wseq_c2), _ = 
        WSeq.pick_wc (mpair_with_worlds w_l w_r) wseq
        |! unwrap "Can't find the mpair in the conlcusion."
        |! Tuple.T2.map1 ~f:match_ws_mpair_exn in
      (* Compute the world state *)
      let ws, _ = 
        WSeq.pick_wc (apair_with_sibling (World.rename_exn rn_new w_r)) wseq
        |! unwrap "Can't find the apair introduced in the premise." in
      let rn_ws = infer_rename_ws ws Map.empty in
      let ws' = apply_rename_ws rn_ws ws in
      (* Compute the split *)
      let wseq_c2', wseq_p' = match_ws_apair_exn ws in
      let { WSeq.tcontext = tc_c1; WSeq.fcontext = fc_c1; WSeq.wcontext = wc_c1 } = 
        WSeq.apply_rename rn_new wseq_c1 |! simpl_unwrap in
      let split = { SBBI.Rule.selected_tc = tc_c1; 
                    SBBI.Rule.selected_fc = fc_c1;
                    SBBI.Rule.selected_wc = (wseq_c2'.WSeq.world, wseq_p'.WSeq.world) :: (List.map ~f:get_names wc_c1) } in
      let w_l', w_r' = World.get_fresh (), World.get_fresh () in
      (* Compute the weakening *)
      let wseq_c2_W_raw = WSeq.remove_tc_mzero_exn wseq_c2 in
      let rn_wseq_c2 = infer_rename_s wseq_c2_W_raw (Map.of_alist_exn [w_r, w_r']) in
      let { WSeq.tcontext = tc_W; WSeq.fcontext = fc_W; WSeq.wcontext = wc_W } = apply_rename_s rn_wseq_c2 wseq_c2_W_raw in
      (* Construct the conclusion *)
      SBuild.construct_exn (SBBI.Build.TP (w_r, w_p)) (SBBI.Proof.POne sproof)
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.WeakW ws') (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (w_l, w_r)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.ZeroD (w_l', w_r', split)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_r', w_l')) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_l', w_p)) (SBBI.Proof.POne sproof))
      |! apply_weakening_tc_exn tc_W
      |! apply_weakening_fc_exn fc_W
      |! apply_weakening_wc_exn wc_W
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (w_r', w_l')) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_l', w_r')) (SBBI.Proof.POne sproof))
      (* The first contraction! *)
      |! (fun sproof -> 
        let _, wseq, _ = sproof in
        let rn_1 = 
          InferRename.compute wseq (w_l, w_r) (w_l', w_r') 
          |! Option.value_exn in
        SBuild.construct_exn (SBBI.Build.ContraW ((w_l, w_r), rn_1)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_r, w_p)) (SBBI.Proof.POne sproof))
      (* The second contraction! *)
      |! (fun sproof -> 
        let _, wseq, _ = sproof in
        let rn_2 = 
          InferRename.compute wseq (w_r, w_p) 
            (World.rename_exn rn_ws (World.rename_exn rn_new w_r), World.rename_exn rn_ws (World.rename_exn rn_new w_p))
          |! Option.value_exn in
        SBuild.construct_exn (SBBI.Build.ContraW ((w_r, w_p), rn_2)) (SBBI.Proof.POne sproof))
      |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (w_l, w_r)) (SBBI.Proof.POne sproof))
    with e -> exn_reraise ~msg:(Error.fails "convert_zero_down") e
  end
  | CSBBI.Rule.Assoc (((w_1n2, w_3), (w_1, w_2)), (w_new, rn_1, rn_2, rn_3)) -> begin
    try
      let cproof = CSBBI.Proof.match_prem_one_exn cprem in
      let _, wseq_prem, _ as sproof = convert_aux cproof in
      (* T; (T'; W1, W2 => D'), W3; W1',(W2',W3'=> none ) => D *)
      (* Obtain the basic information *)
      let (wseq_1n2, wseq_3), wseq_p' = 
        WSeq.pick_wc_exn (mpair_with_worlds w_1n2 w_3) wseq_prem 
        |! Tuple.T2.map1 ~f:match_ws_mpair_exn in
      let (wseq_1, wseq_2), wseq_r =
        WSeq.pick_wc_exn (mpair_with_worlds w_1 w_2) wseq_1n2
        |! Tuple.T2.map1 ~f:match_ws_mpair_exn in
      (* let { WSeq.world = w_r } = wseq_r in *)
      let { WSeq.world = w_p } as wseq_p = WSeq.remove_wc_mpair_exn (World.rename_exn rn_1 w_1, w_new) wseq_p' in
      let new_w_1n2 = World.get_fresh () in
      (* Construct the conclusion *)
      let sproof_apply_assoc = 
        SBuild.construct_exn (SBBI.Build.Assoc ((World.rename_exn rn_1 w_1, w_new), new_w_1n2)) (SBBI.Proof.POne sproof) in
      (* T; (T'; W1, W2 => D'), W3; (W1',W2'=>none),W3' => D *)
      (* Apply weakening for T' => D' *)
      let rn_W' = infer_rename_s wseq_r Map.empty in
      let { WSeq.tcontext = tc_W'; WSeq.fcontext = fc_W'; WSeq.wcontext = wc_W' } = apply_rename_s rn_W' wseq_r in
      let sproof_apply_weak_w' =
        SBuild.construct_exn (SBBI.Build.TP (World.rename_exn rn_3 w_3, wseq_p.WSeq.world)) (SBBI.Proof.POne sproof_apply_assoc)
        (* W1', W2'; W3'<T; (T'; W1, W2 => D'), W3; => D> => none *)
        |! apply_weakening_tc_exn tc_W'
        |! apply_weakening_fc_exn fc_W'
        |! apply_weakening_wc_exn wc_W' 
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (new_w_1n2, World.rename_exn rn_3 w_3)) (SBBI.Proof.POne sproof)) in
      (* T; (T'; W1, W2 => D'), W3; (T'; W1',W2'=>D'),W3' => D *)
      (* Append S_1 *)
      let rn_S1, new_S1 = 
        infer_and_apply_rename_ws Map.empty (WSeq.Apair (wseq_2, WSeq.add_wc_apair_exn (wseq_3, wseq_p) wseq_r)) in
      let sproof_add_S1 =
        SBuild.construct_exn (SBBI.Build.TP (w_3, w_p)) (SBBI.Proof.POne sproof_apply_weak_w')
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_2, w_1n2)) (SBBI.Proof.POne sproof)) 
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.WeakW new_S1) (SBBI.Proof.POne sproof)) in
      (* Append S_2 *)
      let rn_S2, new_S2 =
        infer_and_apply_rename_ws Map.empty (WSeq.Apair (wseq_1, WSeq.add_wc_apair_exn (wseq_3, wseq_p) wseq_r)) in
      let sproof_add_S2 =
        SBuild.construct_exn (SBBI.Build.TC (w_1, w_2)) (SBBI.Proof.POne sproof_add_S1)
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_2, w_1)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_1, w_1n2)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.WeakW new_S2) (SBBI.Proof.POne sproof)) in
      (* Append S_3 *)
      let rn_S3, new_S3 =
        infer_and_apply_rename_ws Map.empty (WSeq.Apair (WSeq.add_wc_mpair_exn (wseq_1, wseq_2) wseq_r, wseq_p)) in
      let sproof_add_S3 = 
        SBuild.construct_exn (SBBI.Build.TC (w_2, w_1)) (SBBI.Proof.POne sproof_add_S2)
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_1, w_2)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (w_1n2, w_3)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_3, w_1n2)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_1n2, w_p)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.WeakW new_S3) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (w_3, w_1n2)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (wseq_r.WSeq.world, w_3)) (SBBI.Proof.POne sproof)) in

      (* Apply ContractionW *)
      let _, sproof_add_S3_seq, _ = sproof_add_S3 in
      let new_rn = InferRename.compute sproof_add_S3_seq (w_1n2, w_3) (new_w_1n2, World.rename_exn rn_3 w_3) |! Option.value_exn in
      (* TODO: Error here. Correct it if you can *)
      (* let f rn_SN rn_N w = *)
      (*   if Map.has_key rn_SN w then World.rename_exn rn_SN w, World.rename_exn rn_N w *)
      (*   else w, World.rename_exn rn_N w in *)
      (* let new_rn_1 = List.map ~f:(f rn_S1 rn_1) (Map.keys rn_1) |! Map.of_alist_exn in *)
      (* let new_rn_2 = List.map ~f:(f rn_S2 rn_2) (Map.keys rn_2) |! Map.of_alist_exn in *)
      (* let new_rn_3 = List.map ~f:(f rn_S3 rn_3) (Map.keys rn_3) |! Map.of_alist_exn in *)
      (* let new_rn = *)
      (*   Map.add ~key:w_1n2 ~data:new_w_1n2 new_rn_1 *)
      (*   |! Map.merge ~f:merge_nodup new_rn_2 *)
      (*   |! Map.merge ~f:merge_nodup new_rn_3 in *)
      let sproof_first_contra =
        SBuild.construct_exn (SBBI.Build.ContraW ((w_1n2, w_3), new_rn)) (SBBI.Proof.POne sproof_add_S3) in

      (* Append S1_3 & S2_3 & Apply Contraction on S3 *)
      let rn_S1_3, new_S1_3 =
        infer_and_apply_rename_ws Map.empty (WSeq.Apair (wseq_2, WSeq.add_wc_apair_exn (wseq_3, wseq_p) wseq_r)) in
      let rn_S2_3, new_S2_3 =
        infer_and_apply_rename_ws Map.empty (WSeq.Apair (wseq_1, WSeq.add_wc_apair_exn (wseq_3, wseq_p) wseq_r)) in      
      (* let new_rn_S3_1 = List.map ~f:(fun w -> World.rename_exn rn_S1 w, World.rename_exn rn_S1_3 w) (Map.keys rn_S1)  *)
      (*                   |! Map.of_alist_exn in *)
      (* let new_rn_S3_2 = List.map ~f:(fun w -> World.rename_exn rn_S2 w, World.rename_exn rn_S2_3 w) (Map.keys rn_S2)  *)
      (*                   |! Map.of_alist_exn in *)
      (* let new_rn_S3 = Map.merge ~f:merge_nodup new_rn_S3_1 new_rn_S3_2  *)
      (*                 |! Map.merge ~f:merge_right rn_S3 in *)

      let _, sproof_contra_S3'_seq, _ as sproof_contra_S3' = 
        SBuild.construct_exn (SBBI.Build.Comm (w_3, w_1n2)) (SBBI.Proof.POne sproof_first_contra)
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_1n2, w_p)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (w_3, World.rename_exn rn_S3 w_1n2)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (World.rename_exn rn_S3 w_1n2, w_3)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_3, World.rename_exn rn_S3 w_p)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (World.rename_exn rn_S3 w_2, World.rename_exn rn_S3 w_1n2)) 
          (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.WeakW new_S1_3) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (World.rename_exn rn_S3 w_1, World.rename_exn rn_S3 w_2)) 
          (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (World.rename_exn rn_S3 w_2, World.rename_exn rn_S3 w_1))
          (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (World.rename_exn rn_S3 w_1, World.rename_exn rn_S3 w_1n2))
          (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.WeakW new_S2_3) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (World.rename_exn rn_S3 w_2, World.rename_exn rn_S3 w_1))
          (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (World.rename_exn rn_S3 w_1, World.rename_exn rn_S3 w_2))
          (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (World.rename_exn rn_S3 w_1n2, w_3)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_3, World.rename_exn rn_S3 w_1n2)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (World.rename_exn rn_S3 w_1n2, World.rename_exn rn_S3 w_p)) 
          (SBBI.Proof.POne sproof)) in

      let new_rn_S3 = InferRename.compute sproof_contra_S3'_seq (w_1n2, w_p) (World.rename_exn rn_S3 w_1n2, World.rename_exn rn_S3 w_p) 
                      |! Option.value_exn in
      let sproof_contra_S3 = SBuild.construct_exn (SBBI.Build.ContraW ((w_1n2, w_p), new_rn_S3)) (SBBI.Proof.POne sproof_contra_S3') in

      (* Append S1_2 & Apply Contraction on S2 *)
      let rn_S1_2, new_S1_2 =
        infer_and_apply_rename_ws Map.empty (WSeq.Apair (wseq_2, WSeq.add_wc_apair_exn (wseq_3, wseq_p) wseq_r)) in
      (* let new_rn_S2 = List.map ~f:(fun w -> World.rename_exn rn_S1 w, World.rename_exn rn_S1_2 w) (Map.keys rn_S1)  *)
      (*                 |! Map.of_alist_exn  *)
      (*                 |! Map.merge ~f:merge_right rn_S2 in *)
      let _, sproof_contra_S2'_seq, _ as sproof_contra_S2' = 
        SBuild.construct_exn (SBBI.Build.TC (w_3, w_1n2)) (SBBI.Proof.POne sproof_contra_S3)
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_1n2, w_3)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_3, w_p)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_2, w_1)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_1, w_1n2)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (w_2, World.rename_exn rn_S2 w_1)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (World.rename_exn rn_S2 w_1, w_2)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (w_2, World.rename_exn rn_S2 w_1n2)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.WeakW new_S1_2) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TC (World.rename_exn rn_S2 w_1, w_2)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.Comm (w_2, World.rename_exn rn_S2 w_1)) (SBBI.Proof.POne sproof))
        |! (fun sproof -> SBuild.construct_exn (SBBI.Build.TP (World.rename_exn rn_S2 w_1, World.rename_exn rn_S2 w_1n2)) 
          (SBBI.Proof.POne sproof)) in

      let new_rn_S2 = InferRename.compute sproof_contra_S2'_seq (w_1, w_1n2) (World.rename_exn rn_S2 w_1, World.rename_exn rn_S2 w_1n2) 
                      |! Option.value_exn in
      let sproof_contra_S2 = SBuild.construct_exn (SBBI.Build.ContraW ((w_1, w_1n2), new_rn_S2)) (SBBI.Proof.POne sproof_contra_S2') in

      (* Apply Contraction on S1 *)
      let sproof_contra_S1 =
        SBuild.construct_prem_exn (SBBI.Build.TC (w_2, w_1)) (SBBI.Proof.POne sproof_contra_S2)
        |! SBuild.construct_prem_exn (SBBI.Build.Comm (w_1, w_2))
        |! SBuild.construct_prem_exn (SBBI.Build.TP (w_2, w_1n2))
        |! SBuild.construct_prem_exn (SBBI.Build.ContraW ((w_2, w_1n2), rn_S1)) 
        |! SBBI.Proof.match_prem_one_exn in
      (* Re-display w as the reference world *)
      SBuild.construct_prem_exn (SBBI.Build.TC (w_1, w_2)) (SBBI.Proof.POne sproof_contra_S1)
      |! SBuild.construct_prem_exn (SBBI.Build.TC (w_1n2, w_3))
      |! SBBI.Proof.match_prem_one_exn
    with e -> 
      Printexc.print_backtrace stdout; exn_reraise ~msg:(Error.fails "convert_assoc") e    
  end

let convert cproof =
  try
    convert_aux cproof |! wrap
  with e -> exn_wrap_err ~msg:(Error.fails "ConvertCS.convert") e

let convert_exn cproof = 
  try
    convert cproof |! simpl_unwrap
  with 
  | Failure msg -> 
    let () = print_string msg |! print_newline in
    exn_failure "ConvertCS.convert"    

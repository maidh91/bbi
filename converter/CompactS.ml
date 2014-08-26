open Core.Std
open Common
open Option

(* To Common.ml *)
let is_okay = function
  | Ok _    -> true
  | Error _ -> false

(* To WSeq.ml *)
let mpair_with_worlds w_A w_B = function
  | WSeq.Mpair (wseq_A, wseq_B) ->
    World.eq w_A wseq_A.WSeq.world && World.eq w_B wseq_B.WSeq.world
  | _ -> false

let apair_with_worlds w_A w_B = function
  | WSeq.Apair (wseq_A, wseq_B) ->
    World.eq w_A wseq_A.WSeq.world && World.eq w_B wseq_B.WSeq.world
  | _ -> false

let wstate_with_worlds w_A w_B = function
  | WSeq.Mpair (s_A, s_B)
  | WSeq.Apair (s_A, s_B) -> 
    World.eq w_A s_A.WSeq.world 
    && World.eq w_B s_B.WSeq.world

let get_names = function
  | WSeq.Mpair (w_1, w_2) -> w_1.WSeq.world, w_2.WSeq.world
  | WSeq.Apair (w_1, w_2) -> w_1.WSeq.world, w_2.WSeq.world

(* To ProofBuild.ml *)
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
      wrap (rule, seq, prem)
    end
    | Spec.Proof.POne proof -> begin
      let rule, seq = forward_exn desc (Spec.Rule.POne (goal_of proof)) in
      wrap (rule, seq, prem)
    end
    | Spec.Proof.PTwo (proof_1, proof_2) -> begin
      let rule, seq = forward_exn desc (Spec.Rule.PTwo (goal_of proof_1, goal_of proof_2) )in
      wrap (rule, seq, prem)
    end
  let construct_exn desc prem = construct desc prem |! simpl_unwrap
  let construct_prem_exn desc prem = Spec.Proof.POne (construct_exn desc prem)
end

module SBuild = Make (SBBI)

(** To  SBBI.Build??? *)
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

(** Subsumption *)
let rec pick f = function
  | []       -> None
  | hd :: tl ->
    if f hd then Some tl else (pick f tl) >>| (fun l' -> hd :: l')

let rec subsume_l ~f l_1 l_2 = 
  match l_1 with
  | []          -> Some l_2
  | hd_1 :: l_1' -> 
    (pick (fun hd_2 -> f hd_1 hd_2) l_2) 
    >>= (fun l_2' -> subsume_l ~f:f l_1' l_2')

let eq_ws ws_1 ws_2 =
  match ws_1, ws_2 with
  | WSeq.Mpair (s_1, s_2), WSeq.Mpair (s_1', s_2') 
  | WSeq.Apair (s_1, s_2), WSeq.Apair (s_1', s_2') ->
    (WSeq.eq s_1 s_1' |! is_okay) && (WSeq.eq s_2 s_2' |! is_okay)
  | _ -> false

let subsume s_1 s_2 =
  if World.eq s_1.WSeq.world s_2.WSeq.world then begin
    try
      let tc_diff = subsume_l ~f:(=) s_1.WSeq.tcontext s_2.WSeq.tcontext |! Option.value_exn in
      let fc_diff = subsume_l ~f:(=) s_1.WSeq.fcontext s_2.WSeq.fcontext |! Option.value_exn in
      let wc_diff = subsume_l ~f:eq_ws s_1.WSeq.wcontext s_2.WSeq.wcontext |! Option.value_exn in
      Some (tc_diff, fc_diff, wc_diff)
    with _ -> None
  end else None

(** Existence & Elimination  *)
let rec exists_tc (st, w) s =
  if World.eq w s.WSeq.world then begin
    match st with
    | WSeq.Prop prop -> WSeq.exists_tc_prop prop s |! is_okay
    | WSeq.Mzero     -> WSeq.exists_tc_mzero s |! is_okay
  end else begin
    let exists_tc_aux = function
      | WSeq.Mpair (s_1, s_2) 
      | WSeq.Apair (s_1, s_2) -> 
        exists_tc (st, w) s_1 
        || exists_tc (st, w) s_2  
    in List.exists ~f:exists_tc_aux s.WSeq.wcontext
  end
                          
let rec exists_fc (prop, w) s =
  if World.eq w s.WSeq.world then 
    WSeq.exists_fc prop s |! is_okay 
  else begin
    let exists_fc_aux = function
      | WSeq.Mpair (s_1, s_2) 
      | WSeq.Apair (s_1, s_2) -> 
        exists_fc (prop, w) s_1 
        || exists_fc (prop, w) s_2  
    in List.exists ~f:exists_fc_aux s.WSeq.wcontext
  end

let rec exists_mpair (w_c1, w_c2) s =
  let exists_mpair_aux = function
    | WSeq.Mpair (s_1, s_2) 
    | WSeq.Apair (s_1, s_2) ->
      exists_mpair (w_c1, w_c2) s_1
      || exists_mpair (w_c1, w_c2) s_2 
  in (List.exists ~f:(mpair_with_worlds w_c1 w_c2) s.WSeq.wcontext) 
  || (List.exists ~f:exists_mpair_aux s.WSeq.wcontext)

let rec exists_apair (w_s, w_p) s =
  let exists_apair_aux = function
    | WSeq.Mpair (s_1, s_2) 
    | WSeq.Apair (s_1, s_2) ->
      exists_apair (w_s, w_p) s_1
      || exists_apair (w_s, w_p) s_2 
  in (List.exists ~f:(apair_with_worlds w_s w_p) s.WSeq.wcontext) 
  || (List.exists ~f:exists_apair_aux s.WSeq.wcontext)

let exists_tc_ws (st, w) = function
  | WSeq.Mpair (s_1, s_2) 
  | WSeq.Apair (s_1, s_2) ->
    exists_tc (st, w) s_1 
    || exists_tc (st, w) s_2
                          
let exists_fc_ws (prop, w) = function
  | WSeq.Mpair (s_1, s_2) 
  | WSeq.Apair (s_1, s_2) ->
    exists_fc (prop, w) s_1 
    || exists_fc (prop, w) s_2

let exists_mpair_ws (w_c1, w_c2) = function
  | WSeq.Mpair (s_1, s_2) ->
    (exists_mpair (w_c1, w_c2) s_1) 
    || (exists_mpair (w_c1, w_c2) s_2)
  | WSeq.Apair (s_1, s_2) ->
    (exists_mpair (w_c1, w_c2) s_1) 
    || (exists_mpair (w_c1, w_c2) s_2)

let exists_apair_ws (w_s, w_p) = function
  | WSeq.Mpair (s_1, s_2) ->
    (exists_apair (w_s, w_p) s_1) 
    || (exists_apair (w_s, w_p) s_2)
  | WSeq.Apair (s_1, s_2) ->
    (exists_apair (w_s, w_p) s_1) 
    || (exists_apair (w_s, w_p) s_2)

let rec remove_tc_exn (st, w) s =
  if World.eq w s.WSeq.world then begin
    match st with
    | WSeq.Prop prop -> WSeq.remove_tc_prop_exn prop s
    | WSeq.Mzero     -> WSeq.remove_tc_mzero_exn s
  end else begin
    let remove_tc_exn_aux = function
      | WSeq.Mpair (s_1, s_2) -> WSeq.Mpair (remove_tc_exn (st, w) s_1, remove_tc_exn (st, w) s_2)
      | WSeq.Apair (s_1, s_2) -> WSeq.Apair (remove_tc_exn (st, w) s_1, remove_tc_exn (st, w) s_2)  
    in { s with WSeq.wcontext = List.map ~f:remove_tc_exn_aux s.WSeq.wcontext }
  end

let rec remove_fc_exn (prop, w) s =
  if World.eq w s.WSeq.world then WSeq.remove_fc_exn prop s
  else begin
    let remove_fc_exn_aux = function
      | WSeq.Mpair (s_1, s_2) -> WSeq.Mpair (remove_fc_exn (prop, w) s_1, remove_fc_exn (prop, w) s_2)
      | WSeq.Apair (s_1, s_2) -> WSeq.Apair (remove_fc_exn (prop, w) s_1, remove_fc_exn (prop, w) s_2)  
    in { s with WSeq.wcontext = List.map ~f:remove_fc_exn_aux s.WSeq.wcontext }
  end

let rec remove_apair_exn (w_s, w_p) s =
  if WSeq.exists_wc_apair (w_s, w_p) s |! is_okay then WSeq.remove_wc_apair_exn (w_s, w_p) s
  else begin
    let remove_apair_exn_aux = function
      | WSeq.Mpair (s_1, s_2) -> WSeq.Mpair (remove_apair_exn (w_s, w_p) s_1, remove_apair_exn (w_s, w_p) s_2)
      | WSeq.Apair (s_1, s_2) -> WSeq.Apair (remove_apair_exn (w_s, w_p) s_1, remove_apair_exn (w_s, w_p) s_2)
    in { s with WSeq.wcontext = List.map ~f:remove_apair_exn_aux s.WSeq.wcontext }
  end

let rec remove_mpair_exn (w_c1, w_c2) s =
  if WSeq.exists_wc_mpair (w_c1, w_c2) s |! is_okay then WSeq.remove_wc_mpair_exn (w_c1, w_c2) s
  else begin
    let remove_mpair_exn_aux = function
      | WSeq.Mpair (s_1, s_2) -> WSeq.Mpair (remove_mpair_exn (w_c1, w_c2) s_1, remove_mpair_exn (w_c1, w_c2) s_2)
      | WSeq.Apair (s_1, s_2) -> WSeq.Apair (remove_mpair_exn (w_c1, w_c2) s_1, remove_mpair_exn (w_c1, w_c2) s_2)
    in { s with WSeq.wcontext = List.map ~f:remove_mpair_exn_aux s.WSeq.wcontext }
  end

let remove_tc_split st sp =
  let rec remove_tc_from_split_aux st = function
    | [] -> exn_failure "A given split does not contain the expected state in selected_tc!"
    | st' :: selected_tc' -> 
      if st = st' then selected_tc' 
      else st' :: (remove_tc_from_split_aux st selected_tc') 
  in { sp with SBBI.Rule.selected_tc = remove_tc_from_split_aux st sp.SBBI.Rule.selected_tc }

let remove_fc_split prop sp =
  let rec remove_fc_from_split_aux prop = function
    | [] -> exn_failure "A given split does not contain the expected proposition in selected_fc!"
    | prop' :: selected_fc' -> 
      if prop = prop' then selected_fc' 
      else prop' :: (remove_fc_from_split_aux prop selected_fc') 
  in { sp with SBBI.Rule.selected_fc = remove_fc_from_split_aux prop sp.SBBI.Rule.selected_fc }

let remove_wc_split (w_1, w_2) sp =
  let rec remove_wc_from_split_aux (w_1, w_2) = function
    | [] -> exn_failure "A given split does not contain the expected wstate in selected_wc!"
    | (w_1', w_2') :: selected_wc' -> 
      if World.eq w_1 w_1' && World.eq w_2 w_2' then selected_wc' 
      else (w_1', w_2') :: (remove_wc_from_split_aux (w_1, w_2) selected_wc') 
  in { sp with SBBI.Rule.selected_wc = remove_wc_from_split_aux (w_1, w_2) sp.SBBI.Rule.selected_wc }

let strengthen_left_update_rule st = function
  | SBBI.Rule.ZeroU (sp, (w_n, w_e)) ->
    SBBI.Rule.ZeroU (remove_tc_split st sp, (w_n, w_e))
  | SBBI.Rule.AndR (prop, sp) ->
    SBBI.Rule.AndR (prop, remove_tc_split st sp)
  | SBBI.Rule.OrL (prop, sp) ->
    SBBI.Rule.OrL (prop, remove_tc_split st sp)
  | SBBI.Rule.ImplyL (prop, sp) ->
    SBBI.Rule.ImplyL (prop, remove_tc_split st sp)
  | r -> r

let strengthen_right_update_rule prop = function
  | SBBI.Rule.ZeroU (sp, (w_n, w_e)) ->
    SBBI.Rule.ZeroU (remove_fc_split prop sp, (w_n, w_e))
  | SBBI.Rule.AndR (prop', sp) ->
    SBBI.Rule.AndR (prop', remove_fc_split prop sp)
  | SBBI.Rule.OrL (prop', sp) ->
    SBBI.Rule.OrL (prop', remove_fc_split prop sp)
  | SBBI.Rule.ImplyL (prop', sp) ->
    SBBI.Rule.ImplyL (prop', remove_fc_split prop sp)
  | r -> r

let strengthen_wstate_update_rule (w_1, w_2) = function
  | SBBI.Rule.ZeroU (sp, (w_n, w_e)) ->
    SBBI.Rule.ZeroU (remove_wc_split (w_1, w_2) sp, (w_n, w_e))
  | SBBI.Rule.AndR (prop', sp) ->
    SBBI.Rule.AndR (prop', remove_wc_split (w_1, w_2) sp)
  | SBBI.Rule.OrL (prop', sp) ->
    SBBI.Rule.OrL (prop', remove_wc_split (w_1, w_2) sp)
  | SBBI.Rule.ImplyL (prop', sp) ->
    SBBI.Rule.ImplyL (prop', remove_wc_split (w_1, w_2) sp)
  | r -> r

(** strengthen_left_for (WSeq.state * World.t) -> SBBI.Proof.t -> SBBI.Proof.t option *)
let rec strengthen_left_for (st, w) (r, s, prem) = 
  if not (exists_tc (st, w) s) then None 
  else begin 
    match r with
    (* Case 1. *)
    | SBBI.Rule.WeakL st' -> 
      let sproof' = SBBI.Proof.match_prem_one_exn prem in
      
      if not (st = st') || not (World.eq w s.WSeq.world) then 
        (strengthen_left_for (st, w) sproof')
         >>| (fun sproof_s' -> r, remove_tc_exn (st, w) s, SBBI.Proof.POne sproof_s')
      else 
        some sproof'
    (* Case 2. *)
    | SBBI.Rule.WeakW (w_1, w_2) -> 
      let sproof' = SBBI.Proof.match_prem_one_exn prem in
      let ws, _ = WSeq.pick_wc_exn (wstate_with_worlds w_1 w_2) s in
      
      if exists_tc_ws (st, w) ws then 
        some (r, remove_tc_exn (st, w) s, SBBI.Proof.POne sproof') 
      else 
        (strengthen_left_for (st, w) sproof')
         >>| (fun sproof_s' -> r, remove_tc_exn (st, w) s, SBBI.Proof.POne sproof_s')                         
    (* Case 3. *)
    | SBBI.Rule.ContraW (w_1, w_2, rn) ->
      let sproof' = SBBI.Proof.match_prem_one_exn prem in
      let ws, _ = WSeq.pick_wc_exn (wstate_with_worlds w_1 w_2) s in
      let guarded cond f v = if cond then f v else Some v in

      (strengthen_left_for (st, w) sproof')
      >>= (guarded (exists_tc_ws (st, w) ws) (fun sproof -> strengthen_left_for (st, World.rename_exn rn w) sproof))
      >>| (fun sproof_s' -> r, remove_tc_exn (st, w) s, SBBI.Proof.POne sproof_s')
    (* Case 4. Should be refined. *)
    | SBBI.Rule.ContraL st' -> 
      if not (st = st') || not (World.eq w s.WSeq.world) then
        let sproof' = SBBI.Proof.match_prem_one_exn prem in
        (strengthen_left_for (st, w) sproof')
         >>| (fun sproof_s' -> r, remove_tc_exn (st, w) s, SBBI.Proof.POne sproof_s')
      else None
    (* Case 5. *)
    | SBBI.Rule.ZeroU (sp, (w_n, w_e)) -> begin
      let sproof' = SBBI.Proof.match_prem_one_exn prem in

      match strengthen_left_for (st, w) sproof' with
      | Some sproof_s' -> 
        let r' = strengthen_left_update_rule st r in
        Some (r', remove_tc_exn (st, w) s, SBBI.Proof.POne sproof_s')
      | None ->
        (strengthen_left_for (st, w_n) sproof')
        >>| (fun sproof_s' -> r, remove_tc_exn (st, w) s, SBBI.Proof.POne sproof_s')
    end
    (* Case 6. *)
    | SBBI.Rule.ZeroD (w_1, w_2) -> 
      let sproof' = SBBI.Proof.match_prem_one_exn prem in
      let w' = if World.eq w w_1 then s.WSeq.world else w in
      
      (strengthen_left_for (st, w') sproof')
      >>| (fun sproof_s' -> r, remove_tc_exn (st, w) s, SBBI.Proof.POne sproof_s')    
    (* Other rules *)
    | _ -> begin 
      match prem with
      | SBBI.Proof.PUnit -> None
      | SBBI.Proof.POne sproof' ->
        (strengthen_left_for (st, w) sproof') 
        >>| (fun sproof_s ->  r, remove_tc_exn (st, w) s, SBBI.Proof.POne sproof_s)
      | SBBI.Proof.PTwo (sproof_1, sproof_2) -> begin 
        match strengthen_left_for (st, w) sproof_1 with
        | Some sproof_s1 -> 
          let r' = strengthen_left_update_rule st r in
          Some (r', remove_tc_exn (st, w) s, SBBI.Proof.PTwo (sproof_s1, sproof_2))
        | None -> 
          (strengthen_left_for (st, w) sproof_2) 
          >>| (fun sproof_s2 -> r, remove_tc_exn (st, w) s, SBBI.Proof.PTwo (sproof_1, sproof_s2))
      end                         
    end
  end

(** strengthen_right_for (Prop.t * World.t) -> SBBI.Proof.t -> SBBI.Proof.t option *)
let rec strengthen_right_for (prop, w) (r, s, prem) = 
  if not (exists_fc (prop, w) s) then None 
  else begin 
    match r with
    (* Case 1. *)
    | SBBI.Rule.WeakR prop' -> 
      let sproof' = SBBI.Proof.match_prem_one_exn prem in
      
      if not (prop = prop') || not (World.eq w s.WSeq.world) then 
        (strengthen_right_for (prop, w) sproof')
         >>| (fun sproof_s' -> r, remove_fc_exn (prop, w) s, SBBI.Proof.POne sproof_s')
      else 
        some sproof'
    (* Case 2. *)
    | SBBI.Rule.WeakW (w_1, w_2) -> 
      let sproof' = SBBI.Proof.match_prem_one_exn prem in
      let ws, _ = WSeq.pick_wc_exn (wstate_with_worlds w_1 w_2) s in
      
      if exists_fc_ws (prop, w) ws then 
        some (r, remove_fc_exn (prop, w) s, SBBI.Proof.POne sproof') 
      else 
        (strengthen_right_for (prop, w) sproof')
         >>| (fun sproof_s' -> r, remove_fc_exn (prop, w) s, SBBI.Proof.POne sproof_s')                         
    (* Case 3. *)
    | SBBI.Rule.ContraW (w_1, w_2, rn) ->
      let sproof' = SBBI.Proof.match_prem_one_exn prem in
      let ws, _ = WSeq.pick_wc_exn (wstate_with_worlds w_1 w_2) s in
      
      if exists_fc_ws (prop, w) ws then
        (strengthen_right_for (prop, w) sproof')
         >>= (strengthen_right_for (prop, World.rename_exn rn w))
         >>| (fun sproof_s' -> r, remove_fc_exn (prop, w) s, SBBI.Proof.POne sproof_s')
      else
        (strengthen_right_for (prop, w) sproof')
         >>| (fun sproof_s' -> r, remove_fc_exn (prop, w) s, SBBI.Proof.POne sproof_s')
    (* Case 4. Should be refined. *)
    | SBBI.Rule.ContraR prop' -> 
      if not (prop = prop') || not (World.eq w s.WSeq.world) then
        let sproof' = SBBI.Proof.match_prem_one_exn prem in
        (strengthen_right_for (prop, w) sproof')
         >>| (fun sproof_s' -> r, remove_fc_exn (prop, w) s, SBBI.Proof.POne sproof_s')
      else None
    (* Case 5. *)
    | SBBI.Rule.ZeroU (sp, (w_n, w_e)) -> begin
      let sproof' = SBBI.Proof.match_prem_one_exn prem in

      match strengthen_right_for (prop, w) sproof' with
      | Some sproof_s' -> 
        let r' = strengthen_right_update_rule prop r in
        some (r', remove_fc_exn (prop, w) s, SBBI.Proof.POne sproof_s')
      | None ->
        (strengthen_right_for (prop, w_n) sproof')
        >>| (fun sproof_s' -> r, remove_fc_exn (prop, w) s, SBBI.Proof.POne sproof_s')
    end
    (* Case 6. *)
    | SBBI.Rule.ZeroD (w_1, w_2) -> 
      let sproof' = SBBI.Proof.match_prem_one_exn prem in
      let w' = if World.eq w w_1 then s.WSeq.world else w in
      
      (strengthen_right_for (prop, w') sproof')
      >>| (fun sproof_s' -> r, remove_fc_exn (prop, w) s, SBBI.Proof.POne sproof_s')
    (* Other rules *)
    | _ -> begin 
      match prem with
      | SBBI.Proof.PUnit -> None
      | SBBI.Proof.POne sproof' ->
        (strengthen_right_for (prop, w) sproof') 
        >>| (fun sproof_s ->  r, remove_fc_exn (prop, w) s, SBBI.Proof.POne sproof_s)
      | SBBI.Proof.PTwo (sproof_1, sproof_2) -> begin 
        match strengthen_right_for (prop, w) sproof_1 with
        | Some sproof_s1 -> 
          let r' = strengthen_right_update_rule prop r in
          Some (r', remove_fc_exn (prop, w) s, SBBI.Proof.PTwo (sproof_s1, sproof_2))
        | None -> 
          (strengthen_right_for (prop, w) sproof_2) 
          >>| (fun sproof_s2 -> r, remove_fc_exn (prop, w) s, SBBI.Proof.PTwo (sproof_1, sproof_s2))
      end                         
    end
  end

(** strengthen_mpair_for (World.t * World.t) -> SBBI.Proof.t -> SBBI.Proof.t option *)
let rec strengthen_mpair_for (w_c1, w_c2) (r, s, prem) =
  match r with
  (* Case 2. *)
  | SBBI.Rule.TC (w_1, w_2) 
  | SBBI.Rule.ZeroD (w_1, w_2) -> 
    if not (World.eq w_c1 w_1 && World.eq w_c2 w_2) then
      let sproof' = SBBI.Proof.match_prem_one_exn prem in
      (strengthen_mpair_for (w_c1, w_c2) sproof')
       >>| (fun sproof_s' -> r, remove_mpair_exn (w_c1, w_c2) s, SBBI.Proof.POne sproof_s')
    else None
  (* Case 3. *)
  | SBBI.Rule.WeakW (w_1, w_2) ->
    let sproof' = SBBI.Proof.match_prem_one_exn prem in
    let ws, _ = WSeq.pick_wc_exn (wstate_with_worlds w_1 w_2) s in
    
    if World.eq w_c1 w_1 && World.eq w_c2 w_2 then
      some sproof'
    else if exists_mpair_ws (w_c1, w_c2) ws then 
      some (r, remove_mpair_exn (w_c1, w_c2) s, SBBI.Proof.POne sproof') 
    else 
      (strengthen_mpair_for (w_c1, w_c2) sproof')
       >>| (fun sproof_s' -> r, remove_mpair_exn (w_c1, w_c2) s, SBBI.Proof.POne sproof_s')
  (* Case 4. *)
  | SBBI.Rule.ContraW (w_1, w_2, rn) ->
    let sproof' = SBBI.Proof.match_prem_one_exn prem in
    let ws, _ = WSeq.pick_wc_exn (wstate_with_worlds w_1 w_2) s in

    if World.eq w_c1 w_1 && World.eq w_c2 w_2 then
      None
    else if exists_mpair_ws (w_c1, w_c2) ws then begin
      (strengthen_mpair_for (w_c1, w_c2) sproof') 
      >>= (strengthen_mpair_for (World.rename_exn rn w_c1, World.rename_exn rn w_c2))
      >>| (fun sproof_s' -> r, remove_mpair_exn (w_c1, w_c2) s, SBBI.Proof.POne sproof_s')
    end else 
      (strengthen_mpair_for (w_c1, w_c2) sproof')
       >>| (fun sproof_s' -> r, remove_mpair_exn (w_c1, w_c2) s, SBBI.Proof.POne sproof_s')
  (* Case 5. *)
  | SBBI.Rule.Comm (w_1, w_2) -> 
    let sproof' = SBBI.Proof.match_prem_one_exn prem in
    let w_c1', w_c2' = if World.eq w_c1 w_1 && World.eq w_c2 w_2 then w_c2, w_c1 else w_c1, w_c2 in

    (strengthen_mpair_for (w_c1', w_c2') sproof')
    >>| (fun sproof_s' -> r, remove_mpair_exn (w_c1, w_c2) s, SBBI.Proof.POne sproof_s')
  (* Case 6. *)
  | SBBI.Rule.Assoc ((w_1n2, w_3), _) -> 
    let (s_1n2, _), _ = WSeq.pick_wc_mpair (w_1n2, w_3) s 
                          |! simpl_unwrap in
    
    if World.eq w_c1 w_1n2 && World.eq w_c2 w_3 then
      None
    else if List.exists ~f:(mpair_with_worlds w_c1 w_c2) s_1n2.WSeq.wcontext then
      None
    else begin
      let sproof' = SBBI.Proof.match_prem_one_exn prem in
      (strengthen_mpair_for (w_c1, w_c2) sproof') 
      >>| (fun sproof_s' -> r, remove_mpair_exn (w_c1, w_c2) s, SBBI.Proof.POne sproof_s')
    end
  (* Other cases *)
  | _ -> begin 
    match prem with
    | SBBI.Proof.PUnit -> None
    | SBBI.Proof.POne sproof' ->
      (strengthen_mpair_for (w_c1, w_c2) sproof') 
      >>| (fun sproof_s ->  r, remove_mpair_exn (w_c1, w_c2) s, SBBI.Proof.POne sproof_s)
    | SBBI.Proof.PTwo (sproof_1, sproof_2) -> begin       
      if r = SBBI.Rule.StarR && List.exists ~f:(mpair_with_worlds w_c1 w_c2) s.WSeq.wcontext then None 
      else begin
        match strengthen_mpair_for (w_c1, w_c2) sproof_1 with
        | Some sproof_s1 -> 
          let r' = strengthen_wstate_update_rule (w_c1, w_c2) r in
          Some (r', remove_mpair_exn (w_c1, w_c2) s, SBBI.Proof.PTwo (sproof_s1, sproof_2))
        | None -> 
          (strengthen_mpair_for (w_c1, w_c2) sproof_2) 
          >>| (fun sproof_s2 -> r, remove_mpair_exn (w_c1, w_c2) s, SBBI.Proof.PTwo (sproof_1, sproof_s2))
      end
    end
  end

(** strengthen_apair_for (World.t * World.t) -> SBBI.Proof.t -> SBBI.Proof.t option *)
let rec strengthen_apair_for (w_s, w_p) (r, s, prem) =
  match r with
  (* Case 1. *)
  (* | SBBI.Rule.WandL -> *)
  (*   if List.exists ~f:(apair_with_worlds w_s w_p) s.WSeq.wcontext then  *)
  (*     None  *)
  (*   else  *)
  (*     let sproof' = SBBI.Proof.match_prem_one_exn prem in *)
  (*     (strengthen_apair_for (w_s, w_p) sproof')  *)
  (*      >>| (fun sproof_s' -> r, remove_apair_exn (w_s, w_p) s, SBBI.Proof.POne sproof_s') *)
  (* Case 2. *)
  | SBBI.Rule.TP (w_1, w_2) -> 
    
    if not (World.eq w_s w_1 && World.eq w_p w_2) then
      let sproof' = SBBI.Proof.match_prem_one_exn prem in
      (strengthen_apair_for (w_s, w_p) sproof')
       >>| (fun sproof_s' -> r, remove_apair_exn (w_s, w_p) s, SBBI.Proof.POne sproof_s')
    else None
  (* Case 3. *)
  | SBBI.Rule.WeakW (w_1, w_2) ->
    let sproof' = SBBI.Proof.match_prem_one_exn prem in
    let ws, _ = WSeq.pick_wc_exn (wstate_with_worlds w_1 w_2) s in
    
    if World.eq w_s w_1 && World.eq w_p w_2 then 
      some sproof'
    else if exists_apair_ws (w_s, w_p) ws then 
      some (r, remove_apair_exn (w_s, w_p) s, SBBI.Proof.POne sproof') 
    else 
      (strengthen_apair_for (w_s, w_p) sproof')
       >>| (fun sproof_s' -> r, remove_apair_exn (w_s, w_p) s, SBBI.Proof.POne sproof_s')
  (* Case 4. *)
  | SBBI.Rule.ContraW (w_1, w_2, rn) ->
    let sproof' = SBBI.Proof.match_prem_one_exn prem in
    let ws, _ = WSeq.pick_wc_exn (wstate_with_worlds w_1 w_2) s in

    if World.eq w_s w_1 && World.eq w_p w_2 then
      None
    else if exists_apair_ws (w_s, w_p) ws then begin
      (strengthen_apair_for (w_s, w_p) sproof') 
      >>= (strengthen_apair_for (World.rename_exn rn w_s, World.rename_exn rn w_p))
      >>| (fun sproof_s' -> r, remove_apair_exn (w_s, w_p) s, SBBI.Proof.POne sproof_s')
    end else 
      (strengthen_apair_for (w_s, w_p) sproof')
       >>| (fun sproof_s' -> r, remove_apair_exn (w_s, w_p) s, SBBI.Proof.POne sproof_s')
  (* Other cases. *)
  | _ -> begin 
    match prem with
    | SBBI.Proof.PUnit -> None
    | SBBI.Proof.POne sproof' ->
      (strengthen_apair_for (w_s, w_p) sproof') 
      >>| (fun sproof_s ->  r, remove_apair_exn (w_s, w_p) s, SBBI.Proof.POne sproof_s)
    | SBBI.Proof.PTwo (sproof_1, sproof_2) -> begin 
      if r = SBBI.Rule.WandL && List.exists ~f:(apair_with_worlds w_s w_p) s.WSeq.wcontext then None
      else begin
        match strengthen_apair_for (w_s, w_p) sproof_1 with
        | Some sproof_s1 -> 
          let r' = strengthen_wstate_update_rule (w_s, w_p) r in
          Some (r', remove_apair_exn (w_s, w_p) s, SBBI.Proof.PTwo (sproof_s1, sproof_2))
        | None -> 
          (strengthen_apair_for (w_s, w_p) sproof_2) 
          >>| (fun sproof_s2 -> r, remove_apair_exn (w_s, w_p) s, SBBI.Proof.PTwo (sproof_1, sproof_s2))
      end
    end
  end

            
(** Apply Rename  *)
let invert_rename rn =
  Map.keys rn
  |! List.fold_left ~init:[] ~f:(fun l k -> (World.rename_exn rn k, k) :: l)
  |! Map.of_alist_exn

let apply_rename_w rn w =
  try
    World.rename_exn rn w
  with _ -> w

let rec apply_rename_ws rn = function
  | WSeq.Mpair (wseq_1, wseq_2) -> 
    WSeq.Mpair (apply_rename_s rn wseq_1, apply_rename_s rn wseq_2)
  | WSeq.Apair (wseq_1, wseq_2) -> 
    WSeq.Apair (apply_rename_s rn wseq_1, apply_rename_s rn wseq_2)

and apply_rename_s rn ({WSeq.world = w; WSeq.wcontext = wc} as wseq) =
  { wseq with WSeq.world = apply_rename_w rn w; WSeq.wcontext = List.map ~f:(apply_rename_ws rn) wc }

let rec apply_rename_prem rn = function
  | SBBI.Proof.PUnit -> SBBI.Proof.PUnit
  | SBBI.Proof.POne sproof -> 
    SBBI.Proof.POne (apply_rename_p rn sproof)
  | SBBI.Proof.PTwo (sproof_1, sproof_2) -> 
    SBBI.Proof.PTwo (apply_rename_p rn sproof_1, apply_rename_p rn sproof_2)

and apply_rename_p rn (rule, wseq, prem) = apply_rename_rule rn rule, apply_rename_s rn wseq, apply_rename_prem rn prem

and apply_rename_split rn ({ SBBI.Rule.selected_wc = wc } as sp) = 
    { sp with SBBI.Rule.selected_wc = List.map ~f:(fun (w_1, w_2) -> apply_rename_w rn w_1, apply_rename_w rn w_2) wc }

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
    SBBI.Rule.StarL (prop, (apply_rename_w rn w_A, apply_rename_w rn w_B))
  | SBBI.Rule.StarR -> rule
  | SBBI.Rule.WandL -> rule
  | SBBI.Rule.WandR (prop, (w_A, w_B)) ->
    SBBI.Rule.WandR (prop, (apply_rename_w rn w_A, apply_rename_w rn w_B))
  | SBBI.Rule.TC (w_1, w_2) -> 
    SBBI.Rule.TC (apply_rename_w rn w_1, apply_rename_w rn w_2)
  | SBBI.Rule.TP (w_1, w_2) -> 
    SBBI.Rule.TP (apply_rename_w rn w_1, apply_rename_w rn w_2)
  | SBBI.Rule.WeakL _ -> rule
  | SBBI.Rule.WeakR _ -> rule
  | SBBI.Rule.WeakW (w_1, w_2) -> 
    SBBI.Rule.WeakW (apply_rename_w rn w_1, apply_rename_w rn w_2)
  | SBBI.Rule.ContraL _ -> rule
  | SBBI.Rule.ContraR _ -> rule
  | SBBI.Rule.ContraW (w_1, w_2, rn_new) -> begin
    try
      let rn_new' = 
        Map.fold ~f:(fun ~key:w_s ~data:w_t rn_acc -> Map.add ~key:(apply_rename_w rn w_s) ~data:(apply_rename_w rn w_t) rn_acc)
          ~init:Map.empty rn_new in
      SBBI.Rule.ContraW (apply_rename_w rn w_1, apply_rename_w rn w_2, rn_new')
    with e -> exn_reraise ~msg:(Error.fails "apply_rename_p_contra_w") e
  end
  | SBBI.Rule.Comm (w_1, w_2) -> SBBI.Rule.Comm (apply_rename_w rn w_1, apply_rename_w rn w_2)
  | SBBI.Rule.Assoc ((w_1n2, w_3), w_new) -> 
    SBBI.Rule.Assoc ((apply_rename_w rn w_1n2, apply_rename_w rn w_3), apply_rename_w rn w_new)
  | SBBI.Rule.ZeroU (sp, (w_l, w_r)) ->
    SBBI.Rule.ZeroU (apply_rename_split rn sp, (apply_rename_w rn w_l, apply_rename_w rn w_r))
  | SBBI.Rule.ZeroD (w_l, w_r) ->
    SBBI.Rule.ZeroD (apply_rename_w rn w_l, apply_rename_w rn w_r)      

(** reduce_traverse : SBBI.Proof.t -> SBBI.Proof.t *)
(* reduce_traverse_for : WSeq.t -> SBBI.Proof.t -> SBBI.Proof.t option *)
let rec reduce_traverse_for s' ((r, s, prem) as sproof) = 
  match subsume s s' with
  | Some (tc_d, fc_d, wc_d) ->
    sproof 
    |! apply_weakening_tc_exn tc_d 
    |! apply_weakening_fc_exn fc_d
    |! apply_weakening_wc_exn wc_d
    |! some
  | None -> begin
    match prem with 
    | SBBI.Proof.PUnit -> None
    | SBBI.Proof.POne sproof' -> reduce_traverse_for s' sproof' 
    | SBBI.Proof.PTwo (sproof_1, sproof_2) -> begin
      match reduce_traverse_for s' sproof_1 with
      | Some sproof_r -> Some sproof_r
      | None -> reduce_traverse_for s' sproof_2
    end
  end

(* 
   - We first simply its premise 
   - We then check whether the current goal sequent appears in the reduced derivation! 
 *)
let rec reduce_traverse ((r, s, prem) as sproof) = 
  match prem with
  | SBBI.Proof.PUnit -> sproof
  | SBBI.Proof.POne sproof' -> 
    let sproof_s = reduce_traverse sproof' in
    begin match reduce_traverse_for s sproof_s with
    | Some sproof_r -> sproof_r 
    | None -> (r, s, SBBI.Proof.POne sproof_s)
    end
  | SBBI.Proof.PTwo (sproof_1, sproof_2) -> 
    let sproof_s1 = reduce_traverse sproof_1 in
    let sproof_s2 = reduce_traverse sproof_2 in
    begin match reduce_traverse_for s sproof_s1 with
    | Some sproof_r1 -> sproof_r1
    | None -> 
      begin match reduce_traverse_for s sproof_s2 with
      | Some sproof_r2 -> sproof_r2
      | None -> (r, s, SBBI.Proof.PTwo (sproof_s1, sproof_s2))
      end
    end


(** reduce_weakening *)
let rec reduce_weakening_tc st ((_, s, _) as sproof) =
  let flag =  
    match st with        
    | WSeq.Prop prop -> 
      WSeq.exists_tc_prop prop s |! is_okay
    | WSeq.Mzero -> 
      WSeq.exists_tc_mzero s |! is_okay
  in if flag then begin
    (strengthen_left_for (st, s.WSeq.world) sproof)
    >>| (fun sproof' -> (SBBI.Rule.WeakL st, s, SBBI.Proof.POne sproof'))
  end else None

let rec reduce_weakening_fc prop ((_, s, _) as sproof) =
  if WSeq.exists_fc prop s |! is_okay then begin
    (strengthen_right_for (prop, s.WSeq.world) sproof)
    >>| (fun sproof' -> (SBBI.Rule.WeakR prop, s, SBBI.Proof.POne sproof'))
  end else None

let rec reduce_weakening_wc ws ((_, s, _) as sproof) =
  match ws with
  | WSeq.Apair (s_s, s_p) -> 
    if WSeq.exists_wc_apair (get_names ws) s |! is_okay then
      (strengthen_apair_for (s_s.WSeq.world, s_p.WSeq.world) sproof)
       >>| (fun sproof' -> (SBBI.Rule.WeakW (s_s.WSeq.world, s_p.WSeq.world), s, SBBI.Proof.POne sproof'))
    else None
  | WSeq.Mpair (s_c1, s_c2) -> 
    if WSeq.exists_wc_mpair (get_names ws) s |! is_okay then
      (strengthen_mpair_for (s_c1.WSeq.world, s_c2.WSeq.world) sproof)
       >>| (fun sproof' -> (SBBI.Rule.WeakW (s_c1.WSeq.world, s_c2.WSeq.world), s, SBBI.Proof.POne sproof'))
    else None

let reduce_weakening_permute sproof (r, s, _) = 
  match r with
  | SBBI.Rule.WeakL st -> 
    reduce_weakening_tc st sproof
  | SBBI.Rule.WeakR prop -> 
    reduce_weakening_fc prop sproof
  | SBBI.Rule.WeakW (w_1, w_2) -> 
    let ws, _ = WSeq.pick_wc_exn (wstate_with_worlds w_1 w_2) s in
    reduce_weakening_wc ws sproof
  | _ -> None

let reduce_weakening_aux ((r, s, prem) as sproof) =
  match r with
  | SBBI.Rule.WeakL _ -> None
  | SBBI.Rule.WeakR _ -> None
  | SBBI.Rule.WeakW _ -> None
  | _ -> begin
    match prem with
    | SBBI.Proof.PUnit -> None
    | SBBI.Proof.POne sproof' -> 
      reduce_weakening_permute sproof sproof'
    | SBBI.Proof.PTwo (sproof_1, sproof_2) -> begin
      match reduce_weakening_permute sproof sproof_1 with
      | Some sproof' -> Some sproof'
      | None -> reduce_weakening_permute sproof sproof_2 
    end
  end

let rec reduce_weakening ((r, s, prem) as sproof) =
  match prem with
  | SBBI.Proof.PUnit -> None
  | SBBI.Proof.POne sproof' -> begin
    match reduce_weakening sproof' with
    | Some sproof_s' -> Some (r, s, SBBI.Proof.POne sproof_s')
    | None -> reduce_weakening_aux sproof 
  end
  | SBBI.Proof.PTwo (sproof_1, sproof_2) -> begin
    match reduce_weakening sproof_1 with
    | Some sproof_s1 -> Some (r, s, SBBI.Proof.PTwo (sproof_s1, sproof_2))
    | None -> begin
      match reduce_weakening sproof_2 with
      | Some sproof_s2 -> Some (r, s, SBBI.Proof.PTwo (sproof_1, sproof_s2))
      | None -> reduce_weakening_aux sproof
    end
  end

(* strengthen : SBBI.Proof.t -> SBBI.Proof.t *)
let rec strengthen (r, s, prem) = 
  match r with
  | SBBI.Rule.ContraL ws -> begin    
    let sproof' = SBBI.Proof.match_prem_one_exn prem in
    match strengthen sproof' with
    | Some sproof_s' -> Some (r, s, SBBI.Proof.POne sproof_s') 
    | None -> begin
      match strengthen_left_for (ws, s.WSeq.world) sproof' with
      | Some sproof_s -> Some sproof_s
      | None          -> None
    end
  end
  | SBBI.Rule.ContraR prop -> begin
    let sproof' = SBBI.Proof.match_prem_one_exn prem in
    match strengthen sproof' with
    | Some sproof_s' -> Some (r, s, SBBI.Proof.POne sproof_s')
    | None -> begin
      match strengthen_right_for (prop, s.WSeq.world) sproof' with
      | Some sproof_s -> Some sproof_s
      | None          -> None
    end
  end
  | SBBI.Rule.ContraW (w_1, w_2, rn) -> begin
    let sproof' = SBBI.Proof.match_prem_one_exn prem in
    match strengthen sproof' with
    | Some sproof_s' -> Some (r, s, SBBI.Proof.POne sproof_s')
    | None -> begin
      let ws, _ = WSeq.pick_wc_exn (wstate_with_worlds w_1 w_2) s in
      let f = match ws with WSeq.Mpair _ -> strengthen_mpair_for | _ -> strengthen_apair_for in
      begin
        match f (w_1, w_2) sproof' with
        | Some sproof_s -> Some (apply_rename_p (invert_rename rn) sproof_s)
        | None -> begin
          match f (World.rename_exn rn w_1, World.rename_exn rn w_2) sproof' with
          | Some sproof_s -> Some sproof_s
          | None          -> None
        end
      end
    end
  end
  | _ -> begin
    match prem with
    | SBBI.Proof.PUnit -> None
    | SBBI.Proof.POne sproof' -> begin
      match sproof' |! strengthen with 
      | Some sproof_s' -> Some (r, s, SBBI.Proof.POne sproof_s')
      | None           -> None
    end 
    | SBBI.Proof.PTwo (sproof_1, sproof_2) -> begin
      match sproof_1 |! strengthen with
      | Some sproof_s1 -> Some (r, s, SBBI.Proof.PTwo (sproof_s1, sproof_2))
      | None -> begin
        match sproof_2 |! strengthen with
        | Some sproof_s2 -> Some (r, s, SBBI.Proof.PTwo (sproof_1, sproof_s2))
        | None -> None
      end
    end
  end

and simplify_strengthen sproof = 
  let sproof' = reduce_traverse sproof in
  match strengthen sproof' with
  | Some sproof_s -> simplify_strengthen sproof_s
  | None -> simplify_reduce sproof

and simplify_reduce sproof = 
  let sproof' = reduce_traverse sproof in
  match reduce_weakening sproof' with
  | Some sproof_s -> simplify_strengthen sproof_s
  | None -> sproof'

and simplify sproof = simplify_strengthen sproof

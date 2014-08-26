(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Common
open Proof_tree
open Proof_type
open Core.Std
open Refiner

(* val solve_goal_by_rules : goal -> inter_rule list -> proof_tree option *)
let solve_goal_by_rules goal rules =
  let rec f_aux rs pf = 
    match rs with
    | [] -> pf
    | r::rs' ->
      frontier_map (app_tac (refiner_inter r)) 1 pf
      |! f_aux rs'
  in
  try
    let solution = f_aux rules (leaf goal) in
    if is_complete_proof solution then
      Some solution
    else
      None
  with _ -> None

let rec undo_binary_rule_if_possible pfs =
  if is_complete_pftreestate pfs then
    pfs
  else
    let ori_cursor = cursor_of_pftreestate pfs in
    let branch_pfs = try first_unproven pfs |! traverse 0 with _ -> pfs in
    let after_cursor = cursor_of_pftreestate branch_pfs in
    let branch_pf = branch_pfs |! proof_of_pftreestate in
    match ref_of_proof branch_pf with 
    | _, first::second::_ -> begin
      assert (is_complete_proof first);
      match solve_goal_by_rules (goal_of_proof branch_pf) (serialize_rules first) with
      | None -> pfs
      | Some pf -> 
        let new_pfs = map_pftreestate (fun _ -> pf) branch_pfs in
        if List.length ori_cursor < List.length after_cursor then
          up_until_cursor ori_cursor new_pfs |! undo_binary_rule_if_possible
        else
          new_pfs 
    end
    | _ -> pfs


(** Try to solve by invertible rules ******************************************************************* *)

let first_tc = List.find_map ~f:(fun (w, (ls,_)) -> 
  match ls.Seq.tc_n with 
  | [] -> None
  | prop::_ -> Some (w, prop))

let first_fc = List.find_map ~f:(fun (w, (ls,_)) -> 
  match ls.Seq.fc_n with
  | [] -> None
  | prop::_ -> Some (w, prop))

let rec solve_inv_tc pfs =
  let g = top_goal_of_pftreestate pfs in
  match first_tc g.Seq.all with
  | None -> solve_inv_fc pfs
  (* general init rule *)
  | Some (w,prop) when Seq.exists_fc w prop g ->
    solve_inv_atom (RInit (w, prop, prop)) pfs
  | Some (w,prop) ->
    match prop with
    | Prop.Bot -> solve_inv_atom (RBotL (w, prop)) pfs
    | Prop.Neg _ ->
      solve_pftreestate_count (refiner_inter (RNegL (w, prop))) pfs
      |! first_unproven |! solve_inv_tc
    | Prop.And _ ->
      solve_pftreestate_count (refiner_inter (RAndL (w, prop))) pfs
      |! first_unproven |! solve_inv_tc
    | Prop.Or _ ->
      solve_pftreestate_count (refiner_inter (ROrL (w, prop))) pfs
      |! first_unproven |! solve_inv_tc
    | Prop.Imply _ ->
      solve_pftreestate_count (refiner_inter (RImplyL (w, prop))) pfs
      |! first_unproven |! solve_inv_tc
    | Prop.Star _ ->
      let w1 = World.get_fresh () in
      let w2 = World.get_fresh () in
      let star_rule = refiner_inter (RStarL ((w,prop),(w1,w2))) in
      solve_pftreestate_count star_rule pfs
      |! first_unproven |! solve_inv_tc
    | Prop.Wand _ ->                    (* Postpone WandL *)
      map_pftreestate (fun _ -> leaf (Seq.mark_tc_s w prop g)) pfs
      |! solve_inv_tc
    | Prop.Unit when not (Seq.is_empty w g) ->
      let unit_rule = refiner_inter (RUnitL (w, prop)) in
      let pfs' = solve_pftreestate_count unit_rule pfs
                 |! first_unproven in 
      if Seq.exists_fc w prop g then
        solve_inv_atom (RUnitR (w, prop)) pfs'
      else
        solve_inv_tc pfs'
    (* | Prop.Atom _ when Seq.exists_fc w prop g -> *)
    (*   solve_inv_atom (RInit (w, prop, prop)) pfs *)
    | _ ->
      map_pftreestate (fun _ -> leaf (Seq.mark_tc_r w prop g)) pfs 
      |! solve_inv_tc 
          
and solve_inv_fc pfs =
  let g = top_goal_of_pftreestate pfs in
  match first_fc g.Seq.all with
  | None -> pfs
  (* general init rule *)
  | Some (w,prop) when Seq.exists_tc w prop g ->
    solve_inv_atom (RInit (w, prop, prop)) pfs
  | Some (w,prop) ->
    match prop with
    | Prop.Top -> solve_inv_atom ((RTopR (w, prop))) pfs
    | Prop.Neg _ ->
      solve_pftreestate_count (refiner_inter (RNegR (w, prop))) pfs
      |! first_unproven |! solve_inv_tc
    | Prop.And _ ->
      solve_pftreestate_count (refiner_inter (RAndR (w, prop))) pfs
      |! first_unproven |! solve_inv_fc
    | Prop.Or _ ->
      solve_pftreestate_count (refiner_inter (ROrR (w, prop))) pfs
      |! first_unproven |! solve_inv_fc
    | Prop.Imply _ ->
      solve_pftreestate_count (refiner_inter (RImplyR (w, prop))) pfs
      |! first_unproven |! solve_inv_tc
    | Prop.Wand _ ->
      let w1 = World.get_fresh () in
      let w2 = World.get_fresh () in
      let wand_rule = refiner_inter (RWandR ((w,prop),(w1,w2))) in
      solve_pftreestate_count wand_rule pfs
      |! first_unproven |! solve_inv_tc
    | Prop.Star _ ->                    (* postpone star *)
      map_pftreestate (fun _ -> leaf (Seq.mark_fc_s w prop g)) pfs 
      |! solve_inv_fc
    | Prop.Unit when Seq.is_empty w g ->
      solve_inv_atom (RUnitR (w, prop)) pfs
    (* | Prop.Atom _ when Seq.exists_tc w prop g -> *)
    (*   solve_inv_atom (RInit (w, prop, prop)) pfs *)
    | _ -> 
      map_pftreestate (fun _ -> leaf (Seq.mark_fc_r w prop g)) pfs 
      |! solve_inv_fc

and solve_inv_atom ir pfs =
  let new_pfs = solve_pftreestate_count (refiner_inter ir) pfs in
  if is_complete_pftreestate new_pfs then
    new_pfs
  else  (* there must be a next_subgoal which is the second premise of a binary rule *)
    let reduced_pfs = top_of_tree new_pfs |! undo_binary_rule_if_possible in
    if is_complete_pftreestate reduced_pfs then
      reduced_pfs
    else
      solve_inv_tc (first_unproven reduced_pfs)

(* proof_tree -> proof_tree *)
let solve_inv_dfs_aux pf =
  if is_complete_proof pf then
    pf
  else
    let dummy_pfs = mk_pftreestate_pf pf in
    first_unproven dummy_pfs
    |! solve_inv_tc
    |! top_of_tree 
    |! proof_of_pftreestate

(* pftreestate -> pftreestate *)
let solve_inv = map_pftreestate solve_inv_dfs_aux

(** wandl_starr_split (WandL & StarR) *************************************************************************** *)

let id a = a
let comm (a, b) = (b, a)

let is_star = function
  | Prop.Star _ -> true
  | _ -> false

let is_wand = function
  | Prop.Wand _ -> true
  | _ -> false

let composable_fc prop ls =
  List.mem prop (ls.Seq.fc_n @ ls.Seq.fc_r @ ls.Seq.fc_s @ ls.Seq.fc_d)

let composable_tc prop ls =
  List.mem prop (ls.Seq.tc_n @ ls.Seq.tc_r @ ls.Seq.tc_s @ ls.Seq.tc_d)

let has_left_child comm w goal =
  List.filter_map goal.Seq.all ~f:(fun (wp, (wp_ls,_)) ->
    let rules = List.filter_map wp_ls.Seq.rc ~f:(fun (wl, wr,_) ->
      let wl, wr = comm (wl, wr) in
      if World.eq w wl then
        Some (wp, wr)
      else
        None) in
    Some rules
  ) 
  |! List.flatten
 
let first_applicable_starr_wandl_aux comm goal =
  let find_star w ls prop = 
    match prop with
    | Prop.Star (prop_a, prop_b) ->
      List.find_map ls.Seq.rc ~f:(fun (w1,w2,_) ->
        let w1, w2 = comm (w1, w2) in
        let w1_ls = Seq.find_ls goal w1 in
        let w2_ls = Seq.find_ls goal w2 in
        if not (composable_fc prop_a w1_ls)
          && not (composable_fc prop_b w2_ls)
          && not (is_star prop_a && w1_ls.Seq.rc = [])
          && not (is_star prop_b && w2_ls.Seq.rc = []) then
          Some (RStarR (w, (w1,w2), prop))
        else
          None)
    | _ -> None
  in
  let find_wand w ls prop =
    match prop with
    | Prop.Wand (prop_a, prop_b) ->
      let worlds = has_left_child comm w goal in
      List.find_map worlds ~f:(fun (w2, w1) ->
        let w1_ls = Seq.find_ls goal w1 in
        let w2_ls = Seq.find_ls goal w2 in
        if not (composable_fc prop_a w1_ls)
          && not (composable_tc prop_b w2_ls) 
          && not (is_star prop_a && w1_ls.Seq.rc = []) 
          && not (is_wand prop_b && w2_ls.Seq.rc = []) then
          Some (RWandL (w2, (w,w1), prop))
        else
          None)
    | _ -> None
  in
  List.find_map goal.Seq.all ~f:(fun (w,(ls,_)) ->
    let star_opt = List.find_map ls.Seq.fc_s ~f:(find_star w ls) in
    match star_opt with
    | Some r -> star_opt
    | None -> List.find_map ls.Seq.tc_s ~f:(find_wand w ls)
  )

let starr_wandl_split pfs =
  let g = first_unproven pfs |! top_goal_of_pftreestate in
  let rule = first_applicable_starr_wandl_aux id g in
  match rule with
  | Some r -> 
    let pfs' = solve_pftreestate_count (refiner_inter r) pfs in
    Some pfs'
  | None ->
    (*  *)
    let rule2 = first_applicable_starr_wandl_aux comm g in
    match rule2 with
    | Some (RStarR (w, (w1,w2), prop) as r')
    | Some (RWandL (w, (w1,w2), prop) as r') ->
      let pfs' = solve_pftreestate (refiner_inter (RComm (w, (w2,w1)))) pfs
                 |! solve_pftreestate_count (refiner_inter r') in
      Some pfs'
    | Some _ -> assert false
    | None -> None

(** Assoc ********************************************************************************************* *)

(* visible_only: 
   true : apply to candidate with priority 1.
   false : apply to candidate with priority 0. *)
let applicable_assoc_aux comm1 comm2 goal visible_only f =
  List.iter goal.Seq.all ~f:(fun (w,(ls,_)) ->
    List.iter ls.Seq.rc ~f:(fun (w', w3, p1) -> 
      let w', w3 = comm1 (w', w3) in
      let w'_ls = Seq.find_ls goal w' in
      List.iter w'_ls.Seq.rc ~f:(fun (w1, w2, p2) ->
        if visible_only  = (p1=Seq.Pri_one & p2=Seq.Pri_one) then
          let w1, w2 = comm2 (w1, w2) in
          let w'' = World.get_fresh () in
          let rename1 = Seq.make_rename goal in
          let rename2 = Seq.make_rename goal in
          let rename3 = Seq.make_rename goal in
          f (RAssoc ((w, w', w1, w2, w3), 
                     (w'', rename1, rename2, rename3)))
      )
    )
  )
    
(* invariant: incomplete proof *)
(* let assoc_split pfs (f:pftreestate -> pftreestate option) = *)
(* assoc_split : pftreestate -> bool -> (prtreestate -> unit) -> unit *)
(* [assoc_split pfs f] : For each assoc candidates of the first
   unproven goal, apply the assoc rule then apply [f]. *)
let assoc_split pfs visible_only (f:pftreestate -> unit) =
  let g = first_unproven pfs |! top_goal_of_pftreestate in
  (*  *)
  applicable_assoc_aux id id g visible_only (fun r ->
    solve_pftreestate_count (refiner_inter r) pfs
    |! first_unproven |! f);
  (*  *)
  applicable_assoc_aux id comm g visible_only (fun r ->
    match r with
    | RAssoc ((_, w', w1, w2, _), _) ->
      solve_pftreestate (refiner_inter (RComm (w', (w2,w1)))) pfs
      |! solve_pftreestate_count (refiner_inter r)
      |! first_unproven |! f 
    | _ -> assert false);
  (*  *)
  applicable_assoc_aux comm id g visible_only (fun r ->
    match r with
    | RAssoc ((w, w', _, _, w3), _) ->
      solve_pftreestate (refiner_inter (RComm (w, (w3,w')))) pfs
      |! solve_pftreestate_count (refiner_inter r) 
      |! first_unproven |! f
    | _ -> assert false);
  (*  *)
  applicable_assoc_aux comm comm g visible_only (fun r ->
    match r with
    | RAssoc ((w, w', w1, w2, w3), _) ->
      solve_pftreestate (refiner_inter (RComm (w, (w3, w')))) pfs
      |! solve_pftreestate (refiner_inter (RComm (w', (w2, w1))))
      |! solve_pftreestate_count (refiner_inter r) 
      |! first_unproven |! f
    | _ -> assert false)
    

(** ZeroD ********************************************************************************************* *)

let applicable_zerod_aux comm goal visible_only f =
  List.iter goal.Seq.all ~f:(fun (w,(ls,_)) ->
    List.iter ls.Seq.rc ~f:(fun (w1, w2, p) ->
      let w1, w2 = comm (w1, w2) in
      if visible_only = (p = Seq.Pri_one) then
        if Seq.is_empty w2 goal then
          let rename = Seq.make_rename ~rule:(fun w' -> if World.eq w' w1 then w else World.get_fresh ()) goal in
          f (RZeroD (w, (w1,w2), rename))
    )
  )

let zerod_split pfs visible_only f =
  let g = first_unproven pfs |! top_goal_of_pftreestate in
  (*  *)
  applicable_zerod_aux id g visible_only (fun r ->
    solve_pftreestate_count (refiner_inter r) pfs
    |! first_unproven |! f);
  (*  *)
  applicable_zerod_aux comm g visible_only (fun r ->
    match r with
    | RZeroD (w, (w1,w2), _) ->
      solve_pftreestate (refiner_inter (RComm (w, (w2,w1)))) pfs
      |! solve_pftreestate_count (refiner_inter r)
      |! first_unproven |! f
    | _ -> assert false)


(** ZeroU ********************************************************************************************* *)

let applicable_zerou_aux goal visible_only f =
  List.iter goal.Seq.all ~f:(fun (w,(_,ls_p)) ->
    if visible_only = (ls_p = Seq.Pri_one) then 
      (* if List.exists (ls.Seq.fc @ ls.Seq.fc_r) ~f:is_star *)
      (*   || List.exists (ls.Seq.tc @ ls.Seq.tc_r) ~f:is_wand then *)
      let w'' = World.get_fresh () in
      let rename = Seq.make_rename goal in 
      f (RZeroU (w, (w'', rename)))
  )
    
let zerou_split pfs visible_only f =
  let g = first_unproven pfs |! top_goal_of_pftreestate in
  (*  *)
  applicable_zerou_aux g visible_only (fun r ->
    solve_pftreestate_count (refiner_inter r) pfs
    |! first_unproven |! f)
    
(** Automation naive DFS ********************************************************************************** *)

exception Auto_fail
exception Proof_found_dfs of pftreestate

type param = {
  stage2 : bool;
  once_considered : bool;
}

(* precondition: incomplete proof. *)
let rec solve_logical pfs =
  let pfs' = solve_inv pfs in
  if proof_of_pftreestate pfs' |! is_complete_proof then
    raise (Proof_found_dfs pfs')
  else
    match starr_wandl_split pfs' with
    | Some new_pfs ->
      solve_logical new_pfs
    | None ->
      pfs'

(* Solves the whole proof. Returns the proof if it found one. *)
let rec auto_dfs_inv_aux depth param pfs =
  try
    pfs
    |! solve_logical
    |! auto_dfs_split depth param   (* Try to solve first open_goal by Assoc, ZeroD, ZeroU. *)
    |! undo_binary_rule_if_possible
    |! auto_dfs_inv_aux depth param (* Try to sovle the next child subgoal. *)
  with
  | Proof_found_dfs solution -> solution
    
(* precondition: incomplete proof *)
(* Solves the first_unproven goal. *)
and auto_dfs_split depth param pfs =
  if depth = 0 then
    raise Auto_fail
  else
    let cursor = cursor_of_pftreestate pfs in
    let pfs = first_unproven pfs in
    let dummy_pfs = proof_of_pftreestate pfs |! mk_pftreestate_pf in
    try
      if not (depth = 1 && param.stage2 = true && param.once_considered = false) then begin
        assoc_split dummy_pfs true (fun pfs ->
          try
            let solution = auto_dfs_inv_aux (depth-1) param pfs |! top_of_tree in
            raise (Proof_found_dfs solution)
          with
          | Auto_fail -> ());
        zerod_split dummy_pfs true (fun pfs ->
          try
            let solution = auto_dfs_inv_aux (depth-1) param pfs |! top_of_tree in
            raise (Proof_found_dfs solution)
          with
          | Auto_fail -> ());
        zerou_split dummy_pfs true (fun pfs ->
          try
            let solution = auto_dfs_inv_aux (depth-1) param pfs |! top_of_tree in
            raise (Proof_found_dfs solution)
          with
          | Auto_fail -> ())
      end;
      (*  *)
      if param.stage2 then begin
        let new_param = {param with once_considered = true} in
        assoc_split dummy_pfs false (fun pfs ->
          try
            let solution = auto_dfs_inv_aux (depth-1) new_param pfs |! top_of_tree in
            raise (Proof_found_dfs solution)
          with
          | Auto_fail -> ());
        zerod_split dummy_pfs false (fun pfs ->
          try
            let solution = auto_dfs_inv_aux (depth-1) new_param  pfs |! top_of_tree in
            raise (Proof_found_dfs solution)
          with
          | Auto_fail -> ());
        zerou_split dummy_pfs false (fun pfs ->
          try
            let solution = auto_dfs_inv_aux (depth-1) new_param pfs |! top_of_tree in
            raise (Proof_found_dfs solution)
          with
          | Auto_fail -> ())
      end;
      (*  *)
      raise Auto_fail
    with
    | Proof_found_dfs solved_dummy_pfs ->
      map_pftreestate (fun _ -> solved_dummy_pfs |! proof_of_pftreestate) pfs
      |! up_until_cursor cursor

let auto_dfs ~depth pfs =
  let dummy_pfs = mk_pftreestate_pf (proof_of_pftreestate pfs) in
  try
    let param = {stage2=false; once_considered=false} in
    let solution = auto_dfs_inv_aux depth param dummy_pfs in
    map_pftreestate (fun _ -> proof_of_pftreestate solution) pfs
  with
  | Auto_fail ->
    let param2 = {stage2=true; once_considered=false} in
    let solution = auto_dfs_inv_aux depth param2  dummy_pfs in
    map_pftreestate (fun _ -> proof_of_pftreestate solution) pfs

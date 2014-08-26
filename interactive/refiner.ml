(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

(* The following code is modified from Coq 8.3. *)

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Common
open Proof_tree
open Proof_type
open Core.Std


module G = Graph.Imperative.Graph.Abstract(World)
module Com = Graph.Components.Make(G)

let split_into_three seq =
  let ws = Seq.all_worlds seq in
  let g = G.create ~size:(List.length ws) () in
  let world_vertex_map = List.map ws ~f:(fun w -> w, G.V.create w) in
  let () = List.iter world_vertex_map ~f:(fun (_,v) -> G.add_vertex g v) in
  let () = List.iter seq.Seq.all ~f:(fun (w, (ls,_)) ->
      let p = List.Assoc.find_exn world_vertex_map w in
      List.iter ls.Seq.rc ~f:(fun (wl, wr,_) ->
        let lc = List.Assoc.find_exn world_vertex_map wl in
        let rc = List.Assoc.find_exn world_vertex_map wr in
        G.add_edge g p lc;
        G.add_edge g p rc;
      )
  ) in
  match Com.scc_list g with
  | [l1; l2; l3] -> 
    List.map l1 ~f:G.V.label,
    List.map l2 ~f:G.V.label,
    List.map l3 ~f:G.V.label
  | _ -> failwith "split_into_three failed.."
  

(* val split_graph: Seq.seq -> World.t -> World.t -> World.t -> World.t list * World.t list * World.t list *)
(* [split_graph ls w_p w_l w_r] returns three label list of worlds accessible to or from w_p, w_l, or w_r, respectively. *)
(* TODO: do not check w_r is included in l3.. and so on. *)
let split_graph seq w_p w_l w_r =
  let l1, l2, l3 =
    Seq.del_rc w_p (w_l, w_r) seq
    |! split_into_three
  in
  if List.mem w_p l1 then
    if List.mem w_l l2 then l1, l2, l3
    else l1, l3, l2
  else if List.mem w_p l2 then
    if List.mem w_l l1 then l2, l1, l3
    else l2, l3, l1
  else if List.mem w_p l3 then
    if List.mem w_l l1 then l3, l1, l2
    else l3, l2, l1
  else
    assert false


let pf_status pf = pf.open_subgoals

let is_complete pf = (0 = (pf_status pf))

let and_status = List.fold_left ~f:(+) ~init:0

let list_chop n l =
  let rec chop_aux acc = function
    | (0, l2) -> (List.rev acc, l2)
    | (n, (h::t)) -> chop_aux (h::acc) (pred n, t)
    | (_, []) -> failwith "list_chop"
  in
  chop_aux [] (n,l)

let prim_refiner goal rule = 
  try
    match rule with
    | RInit (w, tprop, fprop) ->
      if tprop = fprop && Seq.exists_tc w tprop goal && Seq.exists_fc w fprop goal then []
      else failwith "prim_refiner: Init"
    | RTopR (w, (Prop.Top as fprop)) ->
      if Seq.exists_fc w fprop goal then []
      else failwith "prim_refiner: TopR"
    | RBotL (w, (Prop.Bot as tprop)) ->
      if Seq.exists_tc w tprop goal then []
      else failwith "prim_refiner: BotL"
    | RUnitR (w, (Prop.Unit as fprop)) ->
      if Seq.is_empty w goal && Seq.exists_fc w fprop goal then []
      else failwith "prim_refiner: UnitR"
    | RNegL (w, (Prop.Neg prop as tprop)) -> 
      let goal' = Seq.del_tc w tprop goal in
      [Seq.add_fc w prop goal']
    | RNegR (w, (Prop.Neg prop as fprop)) ->
      let goal' = Seq.del_fc w fprop goal in
      [Seq.add_tc w prop goal']
    | RAndL (w, (Prop.And (prop_a, prop_b) as tprop)) ->
      let goal' = Seq.del_tc w tprop goal in
      [Seq.add_tc w prop_a goal' |! Seq.add_tc w prop_b]
    | RAndR (w, (Prop.And (prop_a, prop_b) as fprop)) ->
      let goal' = Seq.del_fc w fprop goal in
      [Seq.add_fc w prop_a goal'; Seq.add_fc w prop_b goal']
    | ROrL (w, (Prop.Or (prop_a, prop_b) as tprop)) ->
      let goal' = Seq.del_tc w tprop goal in
      [Seq.add_tc w prop_a goal'; Seq.add_tc w prop_b goal']
    | ROrR (w, (Prop.Or (prop_a, prop_b) as fprop)) ->
      let goal' = Seq.del_fc w fprop goal in
      [Seq.add_fc w prop_a goal' |! Seq.add_fc w prop_b]
    | RImplyL (w, (Prop.Imply (prop_a, prop_b) as tprop)) ->
      let goal' = Seq.del_tc w tprop goal in
      [Seq.add_fc w prop_a goal'; Seq.add_tc w prop_b goal']
    | RImplyR (w, (Prop.Imply (prop_a, prop_b) as fprop)) -> 
      let goal' = Seq.del_fc w fprop goal in
      [Seq.add_tc w prop_a goal' |! Seq.add_fc w prop_b]
    | RUnitL (w, (Prop.Unit as tprop)) ->
      let goal' = Seq.del_tc w tprop goal in
      [Seq.add_ew w goal']
    | RStarL ((w, (Prop.Star (prop_a, prop_b) as tprop)), (w1, w2)) ->
      (* TODO: have to check w1 and w2 are fresh? *)
      let goal' = Seq.del_tc w tprop goal in
      let pri = if Seq.is_hidden w goal then Seq.Pri_zero else Seq.Pri_one in
      let w1_seq = w1, ({Seq.empty_ls with Seq.tc_n=[prop_a]}, pri) in
      let w2_seq = w2, ({Seq.empty_ls with Seq.tc_n=[prop_b]}, pri) in
      let goal'' = Seq.add_rc w (w1, w2, pri) goal' in
      [Seq.append_ws [w1_seq; w2_seq] goal'']
    | RWandR ((w, (Prop.Wand (prop_a, prop_b) as fprop)), (w1, w2)) ->
      let goal' = Seq.del_fc w fprop goal in
      let pri = if Seq.is_hidden w goal then Seq.Pri_zero else Seq.Pri_one in
      let w1_seq = w1, ({Seq.empty_ls with Seq.tc_n=[prop_a]}, pri) in
      let w2_seq = w2, ({Seq.empty_ls with 
        Seq.rc=[(w,w1,pri)]; Seq.fc_n=[prop_b]}, pri) 
      in
      (* [Seq.append_ws [w1_seq; w2_seq] goal'] *)
      [Seq.cons_w w2_seq goal' |! Seq.cons_w w1_seq]
    | RComm (w, wpair) -> 
      [Seq.comm_rc w wpair goal]
    | RZeroU (w, (w'', rename)) ->
      let goal' = Seq.apply_rename rename goal in
      let phi_w = World.rename_exn rename w in
      let w''_seq = w'', ({Seq.empty_ls with Seq.ew = 1}, Seq.Pri_one) in
      let goal'' = Seq.add_rc w (phi_w, w'', Seq.Pri_one) goal in
      [Seq.cons_w w''_seq goal' |! Seq.merge_seq goal'']
    | RZeroD (w, (w1,w2), rename) ->
      if Seq.is_empty w2 goal && Seq.exists_rc w (w1,w2) goal then
        (* let w_acc, w1_acc, w2_acc = split_graph goal w w1 w2 in *)
        let goal' = Seq.apply_rename rename goal in
        (* hide all relations in the the original nodes *)
        let all_worlds = Seq.all_worlds goal in
        let ori_goal_hidden = Seq.hide_ws all_worlds goal in
        (* merge two nodes: w & w1 *)
        let w_ls = Seq.find_ls ori_goal_hidden w in
        let w_ls' = Seq.find_ls goal' w in
        let w_seq = w, (Seq.merge_local_seq w_ls w_ls', Seq.Pri_one) in
        (* merge two sequents *)
        let ori_goal_hidden_e = Seq.del_w ori_goal_hidden w in
        let goal'_e = Seq.del_w goal' w in
        [Seq.cons_w w_seq goal'_e 
         |! Seq.merge_seq ori_goal_hidden_e
        ]
      else
        failwith "prim_refiner: ZeroD"
    | RStarR (w, (w1,w2), (Prop.Star (prop_a, prop_b) as fprop)) ->
      if Seq.exists_rc w (w1,w2) goal && Seq.exists_fc w fprop goal then
        [Seq.add_fc w1 prop_a goal; Seq.add_fc w2 prop_b goal]
      else
        failwith "prim_refiner: StarR"
    | RWandL (w2, (w,w1), (Prop.Wand (prop_a, prop_b) as tprop)) ->
      if Seq.exists_rc w2 (w,w1) goal && Seq.exists_tc w tprop goal then
        [Seq.add_fc w1 prop_a goal; Seq.add_tc w2 prop_b goal]
      else
        failwith "prim_refiner: WandL"
    | RAssoc ((w, w', w1, w2, w3), (w'', rename1, rename2, rename3)) ->
      if Seq.exists_rc w (w', w3) goal && Seq.exists_rc w' (w1, w2) goal then
        let w_acc, w'_acc, w3_acc = split_graph goal w w' w3 in
        let w'_acc_more, w1_acc, w2_acc = split_graph goal w' w1 w2 in
        let goal1 = Seq.hide_ws w'_acc_more goal 
                    |! Seq.hide_ws w2_acc 
                    |! Seq.apply_rename rename1 in
        let goal2 = Seq.hide_ws w'_acc_more goal 
                    |! Seq.hide_ws w1_acc 
                    |! Seq.apply_rename rename2 in
        let goal3 = Seq.hide_ws w_acc goal 
                    |! Seq.hide_ws w'_acc 
                    |! Seq.apply_rename rename3 in
        let w1' = World.rename_exn rename1 w1 in
        let w2' = World.rename_exn rename2 w2 in
        let w3' = World.rename_exn rename3 w3 in
        let w''_seq = w'',({Seq.empty_ls with Seq.rc=[w2',w3',Seq.Pri_one]},Seq.Pri_one) in
        let goal' = Seq.hide_ws w'_acc goal 
                    |! Seq.hide_ws w3_acc 
                    |! Seq.hide_rc w (w',w3) 
                    |! Seq.add_rc w (w1', w'', Seq.Pri_one) in
        [Seq.merge_seq goal2 goal3
         |! Seq.merge_seq goal1
         |! Seq.cons_w w''_seq
         |! Seq.merge_seq goal']
      else
        failwith "prim_refiner: Assoc"
    | _ -> failwith "Ill-formed rule"
  with
  | Failure msg -> failwith ("prim_refiner: " ^ msg)
    
(* refiner_inter r is a tactic applying the inter_rule r *)
let refiner_inter ir =
  (fun goal ->
    (prim_refiner goal ir,
     (fun spfl ->
       { open_subgoals = and_status (List.map spfl ~f:pf_status);
         goal = goal;
         ref = Some(ir,spfl) })))

(* refiner r is a tactic applying the rule r *)
let refiner r =
  (fun goal -> 
    let ir = rule_to_inter_rule goal r in
    refiner_inter ir goal)

(* [mapshape [ l1 ; ... ; lk ] [ v1 ; ... ; vk ] [ p_1 ; .... ; p_(l1+...+lk) ]]
   gives
   [ (v1 [p_1 ... p_l1]) ; (v2 [ p_(l1+1) ... p_(l1+l2) ]) ; ... ;
   (vk [ p_(l1+...+l(k-1)+1) ... p_(l1+...lk) ]) ]
 *)
let rec mapshape nl (fl : (proof_tree list -> proof_tree) list)
                    (l : proof_tree list) =
  match nl with
    | [] -> []
    | h::t ->
    let m,l = list_chop h l in
    (List.hd_exn fl m) :: (mapshape t (List.tl_exn fl) l)

(* [frontier : proof_tree -> goal list * validation]
   given a proof [p], [frontier p] gives [(l,v)] where [l] is the list of goals
   to be solved to complete the proof, and [v] is the corresponding
   validation *)
let rec frontier p =
  match p.ref with
    | None ->
    ([p.goal],
     (fun lp' ->
        let p' = List.hd_exn lp' in
        Seq.eq p'.goal p.goal |! unwrap "frontier";
        p'))
    | Some(r,pfl) ->
        let gll,vl = List.split (List.map pfl ~f:frontier) in
        (List.flatten gll,
         (fun retpfl ->
            let pfl' = mapshape (List.map gll ~f:List.length) vl retpfl in
            { p with
              open_subgoals = and_status (List.map pfl' ~f:pf_status);
              ref = Some(r,pfl')}))

(* [list_pf p] is the lists of goals to be solved in order to complete the
   proof [p] *)
let list_pf p = fst (frontier p)

let rec frontier_map_rec f n p =
  if n < 1 || n > p.open_subgoals then p else
    match p.ref with
    | None ->
      let p' = f p in
      Seq.eq p'.goal p.goal |! unwrap "frontier_map_rec";
      p'
    | Some(r,pfl) ->
      let (_,rpfl') =
        List.fold_left
          ~f:(fun (n,acc) p -> (n-p.open_subgoals,frontier_map_rec f n p::acc))
          ~init:(n,[]) pfl in
      let pfl' = List.rev rpfl' in
      { p with
        open_subgoals = and_status (List.map pfl' pf_status);
        ref = Some(r,pfl')}
        
(* [frontier_map f n p] applies f on the n-th open subgoal of p and
   rebuilds proof-tree.
   n=1 for first goal, n negative counts from the right *)
let frontier_map f n p =
  let nmax = p.open_subgoals in
  let n = if n < 0 then nmax + n + 1 else n in
  if n < 1 || n > nmax then
    failwith "frontier_map";
  frontier_map_rec f n p

let rec frontier_mapi_rec f i p =
  if p.open_subgoals = 0 then p else
    match p.ref with
    | None ->
      let p' = f i p in
      Seq.eq p'.goal p.goal |! unwrap "frontier_mapi_rec";
      p'
    | Some(r,pfl) ->
      let (_,rpfl') =
        List.fold_left
          ~f:(fun (n,acc) p -> (n+p.open_subgoals,frontier_mapi_rec f n p::acc))
          ~init:(i,[]) pfl in
      let pfl' = List.rev rpfl' in
      { p with
        open_subgoals = and_status (List.map pfl' pf_status);
        ref = Some(r,pfl')}

(* [frontier_mapi f p] applies (f i) on the i-th open subgoal of p. *)
let frontier_mapi f p = frontier_mapi_rec f 1 p


(* leaf g is the canonical incomplete proof of a goal g *)
let leaf g =
  { open_subgoals = 1;
    goal = g;
    ref = None }


(* Functions for handling the state of the proof editor. *)


(* The type of proof-trees state and a few utilities
   A proof-tree state is built from a proof-tree, a set of global
   constraints, and a stack which allows to navigate inside the
   proof-tree remembering how to rebuild the global proof-tree
   possibly after modification of one of the focused children proof-tree.
   The number in the stack corresponds to
   either the selected subtree and the validation is a function from a
   proof-tree list consisting only of one proof-tree to the global
   proof-tree
   or -1 when the move is done behind a registered tactic in which
   case the validation corresponds to a constant function giving back
   the original proof-tree. *)

type pftreestate = {
  tpf      : proof_tree ;
  tstack   : (int * validation) list }

let proof_of_pftreestate pts = pts.tpf
let cursor_of_pftreestate pts = List.map pts.tstack ~f:fst

let is_top_pftreestate pts = pts.tstack = []
let top_goal_of_pftreestate pts = Proof_tree.goal_of_proof pts.tpf

let nth_goal_of_pftreestate n pts =
  let goals = fst (frontier pts.tpf) in
  try List.nth_exn goals (n-1)
  with Invalid_argument _ | Failure _ -> failwith ("No such goal: " ^ string_of_int n)

let descend n p =
  match p.ref with
  | None -> failwith "It is a leaf."
  | Some(r,pfl) ->
    if List.length pfl >= n then begin
      match list_chop (n-1) pfl with
      | left,(wanted::right) ->
        (wanted,
         (fun pfl' ->
           let pf'       = List.hd_exn pfl' in
           let spfl      = left@(pf'::right) in
           let newstatus = and_status (List.map spfl pf_status) in
           { p with
             open_subgoals = newstatus;
             ref           = Some(r,spfl) }))
      | _ -> assert false
    end
    else
      failwith "Too few subproofs"

let traverse n pts = match n with
  | 0 -> begin (* go to the parent *)
    match  pts.tstack with
    | [] -> failwith "traverse: no ancestors"
    | (_,v)::tl ->
      let pf = v [pts.tpf] in
      { tpf = pf;
        tstack = tl;}
  end
  | n -> (* when n>0, go to the nth child *)
    let (npf,v) = descend n pts.tpf in
    { tpf = npf;
      tstack = (n,v):: pts.tstack }

let app_tac tac p =
  let (gll,v) = tac p.goal in
  v (List.map gll ~f:leaf)

(* modify proof state at current position *)
let map_pftreestate f pts =
  { pts with tpf = f pts.tpf}

(* solve the nth subgoal with tactic tac *)
let solve_nth_pftreestate n tac =
  map_pftreestate (fun pt -> frontier_map (app_tac tac) n pt)

let solve_pftreestate =
  solve_nth_pftreestate 1

let num_of_call_ref = ref Big_int.zero_big_int

let solve_pftreestate_count tac = 
  num_of_call_ref := Big_int.succ_big_int !num_of_call_ref;
  solve_nth_pftreestate 1 tac

let num_of_call_solve_pftreestate () = !num_of_call_ref
let reset_num_of_call_solve_pftreestate () = 
  num_of_call_ref := Big_int.zero_big_int

(* logical undoing *)
let weak_undo_pftreestate pts =
  { pts with tpf = leaf pts.tpf.goal }

(* Gives a new proof (a leaf) of a goal gl *)
let mk_pftreestate g =
  { tpf      = leaf g;
    tstack   = []; }

let mk_pftreestate_pf tpf = 
  {tpf=tpf; tstack=[]}

exception Not_found_pf of string

(* Focus on the first leaf proof in a proof-tree state *)
let rec first_unproven pts =
  let pf = (proof_of_pftreestate pts) in
  if is_complete_proof pf then
    (* failwith "first_unproven: No unproven subgoals"; *)
    raise (Not_found_pf "first_unproven: No unproven subgoals");
  if is_leaf_proof pf then
    pts
  else
    let childnum =
      List.findi (children_of_proof pf) ~f:(fun i pf -> not(is_complete_proof pf))
      |! Option.value_exn |! fst |! succ in
    first_unproven (traverse childnum pts)

(* Focus on the last leaf proof in a proof-tree state *)
let rec last_unproven pts =
  let pf = proof_of_pftreestate pts in
  if is_complete_proof pf then
    (* failwith "last_unproven: No unproven subgoals"; *)
    raise (Not_found_pf "last_unproven: No unproven subgoals");
  if is_leaf_proof pf then
    pts
  else
    let children = (children_of_proof pf) in
    let nchilds = List.length children in
    let childnum =
      List.findi (List.rev children) ~f:(fun i pf -> not(is_complete_proof pf))
      |! Option.value_exn |! fst |! succ in
    last_unproven (traverse (nchilds-childnum+1) pts)

let rec nth_unproven n pts =
  let pf = proof_of_pftreestate pts in
  if is_complete_proof pf then
    (* failwith "nth_unproven: No unproven subgoals"; *)
    raise (Not_found_pf "nth_unproven: No unproven subgoals");
  if is_leaf_proof pf then
    if n = 1 then
      pts
    else
      (* failwith "nth_unproven: Not enough unproven subgoals" *)
      raise (Not_found_pf "nth_unproven: Not enough unproven subgoals")
  else
    let children = children_of_proof pf in
    let rec process i k = function
      | [] -> (* failwith "nth_unproven: Not enough unproven subgoals" *)
      raise (Not_found_pf "nth_unproven: Not enough unproven subgoals")
      | pf1::rest ->
        let k1 = pf1.open_subgoals in
        if k1 < k then
          process (i+1) (k-k1) rest
        else
          nth_unproven k (traverse i pts)
    in
    process 1 n children

let rec node_prev_unproven loc pts =
  let pf = proof_of_pftreestate pts in
  if is_complete_proof pf or loc = 1 then
    match cursor_of_pftreestate pts with
    | [] -> (* last_unproven pts (\* roll back *\) *)
      raise (Not_found_pf "No more unproven")
    | n::l ->
      node_prev_unproven n (traverse 0 pts)
  else
    let child = List.nth_exn (children_of_proof pf) (loc - 2) in
    if is_complete_proof child then
      node_prev_unproven (loc - 1) pts
    else
      last_unproven (traverse (loc - 1) pts)

let rec node_next_unproven loc pts =
  let pf = proof_of_pftreestate pts in
  if is_complete_proof pf ||
    loc = (List.length (children_of_proof pf)) then
    match cursor_of_pftreestate pts with
    | [] -> (* first_unproven pts (\* Roll back *\) *)
      raise (Not_found_pf "No more unproven")
    | n::l -> node_next_unproven n (traverse 0 pts)
  else if is_complete_proof (List.nth_exn (children_of_proof pf) loc) then
    node_next_unproven (loc + 1) pts
  else
    first_unproven(traverse (loc + 1) pts)

let next_unproven pts =
  let pf = proof_of_pftreestate pts in
  if is_leaf_proof pf then
    match cursor_of_pftreestate pts with
    | [] -> (* failwith "next_unproven" *)
      raise (Not_found_pf "next_unproven")
    | n::_ -> node_next_unproven n (traverse 0 pts)
  else
    node_next_unproven (List.length (children_of_proof pf)) pts

let prev_unproven pts =
  let pf = proof_of_pftreestate pts in
  if is_leaf_proof pf then
    match cursor_of_pftreestate pts with
    | [] -> (* failwith "prev_unproven" *)
      raise (Not_found_pf "prev_unproven")
    | n::_ -> node_prev_unproven n (traverse 0 pts)
  else
    node_prev_unproven 1 pts

let rec top_of_tree pts =
  if is_top_pftreestate pts then pts else top_of_tree(traverse 0 pts)

let up_until_cursor cursor pfs = 
  let rec up_aux dst_cursor my_cursor pfs =
    match dst_cursor, my_cursor with
    | [], [] -> pfs
    | [], _::mys -> up_aux [] mys (traverse 0 pfs)
    | i::dsts, j::mys when i = j -> up_aux dsts mys pfs
    | _ -> raise (Invalid_argument "The given cursor is not the prefix of the cursor of the pftreestate.")
  in
  up_aux (List.rev cursor) (cursor_of_pftreestate pfs |! List.rev) pfs


let is_complete_pftreestate pts =
  top_of_tree pts |! proof_of_pftreestate |! is_complete_proof (* frontier |! fst |! (\* List.length *\) (=) [] *)


let pftreestate_to_string ?(show_hidden=false)({tpf = pf; tstack=stack} as pts) =
  let unsolved_goals = top_of_tree pts |! proof_of_pftreestate |! status_of_proof in
  string_of_int unsolved_goals ^ " Subgoal(s)\n" ^
  (if stack = [] then "Rooted proof tree is:"
   else ("Proof tree at occurrence [" ^
         (List.rev_map stack ~f:(fun (n,_) -> string_of_int n) |! Core.Core_string.concat ~sep:";") ^
         "] is:")) ^ "\n" ^
    Proof_tree.pr_proof_tree ~show_hidden pf

let pftreestate_to_string_simple ({tpf = pf; tstack=stack} as pts) =
  let unsolved_goals = top_of_tree pts |! proof_of_pftreestate |! status_of_proof in
  string_of_int unsolved_goals ^ " Subgoal(s)\n" ^
  (if stack = [] then "Rooted proof tree is:"
   else ("Proof tree at occurrence [" ^
         (List.rev_map stack ~f:(fun (n,_) -> string_of_int n) |! Core.Core_string.concat ~sep:";") ^
         "] is:")) ^ "\n" ^
    Proof_tree.pr_proof_tree_rules pf

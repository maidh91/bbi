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

open Proof_type
open Core.Std
open Common

let mk_goal seq = seq

let ref_of_proof pf = 
match pf.ref with
| None -> failwith "tactic_of_proof"
| Some r -> r

let rule_of_proof pf = 
let (r,_) = ref_of_proof pf in r

let rec serialize_rules pf =
let (r,cl) = ref_of_proof pf in
List.map cl ~f:serialize_rules
|! List.flatten 
|! List.cons r

let children_of_proof pf =
let (_,cl) = ref_of_proof pf in cl

let goal_of_proof pf = pf.goal

let status_of_proof pf = pf.open_subgoals

let is_complete_proof pf = pf.open_subgoals = 0

let is_leaf_proof pf = (pf.ref = None)

(* Conversion *)
let lptl_to_lpremise = function
| [] -> LBBI.Proof.PUnit
| [t] -> LBBI.Proof.POne t
| [t1; t2] -> LBBI.Proof.PTwo (t1, t2)
| _ -> failwith "Invalid lproof"

let rec to_lproof {open_subgoals; goal; ref} =
match ref with
| None -> failwith "Incomplete proof"
| Some (r, ptl) ->
  let lpremise = List.map ptl ~f:to_lproof |! lptl_to_lpremise in
  let lseq = Seq.to_lseq goal in
  let lrule = 
    match r with
    | RInit (w, prop, _) ->
      LBBI.Rule.Init (prop, w)
    | RTopR (w, _) ->
      LBBI.Rule.TopR w 
    | RBotL (w, _) ->
      LBBI.Rule.BotL w         
    | RNegL (w, prop) ->
      LBBI.Rule.NegL (prop, w)
    | RNegR (w, prop) ->
      LBBI.Rule.NegR (prop, w)
    | RAndL (w, prop) -> 
      LBBI.Rule.AndL (prop, w)
    | RAndR (w, prop) -> 
      LBBI.Rule.AndR (prop, w)
    | ROrL (w, prop) ->
      LBBI.Rule.OrL (prop, w)
    | ROrR (w, prop) ->
      LBBI.Rule.OrR (prop, w)
    | RImplyL (w, prop) ->
      LBBI.Rule.ImplyL (prop, w)
    | RImplyR (w, prop) ->
      LBBI.Rule.ImplyR (prop, w)
    | RUnitL (w, _) ->
      LBBI.Rule.UnitL w
    | RUnitR (w, _) ->
      LBBI.Rule.UnitR w
    | RStarL ((w, prop), (w1, w2)) ->
      LBBI.Rule.StarL ((prop, w), (w1, w2))
    | RWandR ((w, prop), (w1, w2)) ->
      LBBI.Rule.WandR ((prop, w), (w1, w2))
    | RComm (w, (w1, w2)) ->
      LBBI.Rule.Comm ({LSeq.parent=w; LSeq.lchild=w1; LSeq.rchild=w2})
    | RZeroU (w, (new_w, rename)) ->
      LBBI.Rule.ZeroU (w, (new_w, rename))
    | RZeroD (w, (w1,w2), rename) ->
      LBBI.Rule.ZeroD ({LSeq.parent=w; LSeq.lchild=w1; LSeq.rchild=w2}, rename)
    | RStarR (w, (w1,w2), prop) ->
      LBBI.Rule.StarR ({LSeq.parent=w; LSeq.lchild=w1; LSeq.rchild=w2}, prop)
    | RWandL (w2, (w, w1), prop) ->
      LBBI.Rule.WandL ({LSeq.parent=w2; LSeq.lchild=w; LSeq.rchild=w1}, prop)
    | RAssoc ((w, w', w1, w2, w3), (new_w, rename1, rename2, rename3)) ->
      LBBI.Rule.Assoc (
        ({LSeq.parent=w; LSeq.lchild=w'; LSeq.rchild=w3},
         {LSeq.parent=w'; LSeq.lchild=w1; LSeq.rchild=w2}),
        (new_w, rename1, rename2, rename3))
  in
  lrule, lseq, lpremise


let rule_to_inter_rule goal r = 
try 
  match r with
  | Init (ls_idx, tc_idx, fc_idx) ->
    let w = Seq.get_nth_w ls_idx goal in
    let tc_prop = Seq.get_nth_tc ls_idx tc_idx goal in
    let fc_prop = Seq.get_nth_fc ls_idx fc_idx goal in
    RInit (w, tc_prop, fc_prop)
  | TopR (ls_idx, fc_idx) ->
    let w = Seq.get_nth_w ls_idx goal in
    let fprop = Seq.get_nth_fc ls_idx fc_idx goal in
    RTopR (w, fprop)
  | BotL (ls_idx, tc_idx) ->
    let w = Seq.get_nth_w ls_idx goal in
    let tprop = Seq.get_nth_tc ls_idx tc_idx goal in
    RBotL (w, tprop)
  | UnitR (ls_idx, fc_idx) ->
    let w = Seq.get_nth_w ls_idx goal in
    let fprop = Seq.get_nth_fc ls_idx fc_idx goal in
    RUnitR (w, fprop)
  | NegL (ls_idx, tc_idx) ->
    let w = Seq.get_nth_w ls_idx goal in
    let tprop = Seq.get_nth_tc ls_idx tc_idx goal in
    RNegL (w, tprop)
  | NegR (ls_idx, fc_idx) -> 
    let w = Seq.get_nth_w ls_idx goal in
    let fprop = Seq.get_nth_fc ls_idx fc_idx goal in
    RNegR (w, fprop)
  | AndL (ls_idx, tc_idx) -> 
    let w = Seq.get_nth_w ls_idx goal in
    let tprop = Seq.get_nth_tc ls_idx tc_idx goal in
    RAndL (w, tprop)
  | AndR (ls_idx, fc_idx) -> 
    let w = Seq.get_nth_w ls_idx goal in
    let fprop = Seq.get_nth_fc ls_idx fc_idx goal in
    RAndR (w, fprop)
  | OrL (ls_idx, tc_idx) -> 
    let w = Seq.get_nth_w ls_idx goal in
    let tprop = Seq.get_nth_tc ls_idx tc_idx goal in
    ROrL (w, tprop)
  | OrR (ls_idx, fc_idx) -> 
    let w = Seq.get_nth_w ls_idx goal in
    let fprop = Seq.get_nth_fc ls_idx fc_idx goal in
    ROrR (w, fprop)
  | ImplyL (ls_idx, tc_idx) -> 
    let w = Seq.get_nth_w ls_idx goal in
    let tprop = Seq.get_nth_tc ls_idx tc_idx goal in
    RImplyL (w, tprop)
  | ImplyR (ls_idx, fc_idx) -> 
    let w = Seq.get_nth_w ls_idx goal in
    let fprop = Seq.get_nth_fc ls_idx fc_idx goal in
    RImplyR (w, fprop)
  | UnitL (ls_idx, tc_idx) -> 
    let w = Seq.get_nth_w ls_idx goal in
    let tprop = Seq.get_nth_tc ls_idx tc_idx goal in
    RUnitL (w, tprop)
  | StarL (ls_idx, tc_idx) -> 
    let w = Seq.get_nth_w ls_idx goal in
    let tprop = Seq.get_nth_tc ls_idx tc_idx goal in
    let w1 = World.get_fresh () in
    let w2 = World.get_fresh () in
    RStarL ((w, tprop), (w1, w2))
  | WandR (ls_idx, fc_idx) -> 
    let w = Seq.get_nth_w ls_idx goal in
    let fprop = Seq.get_nth_fc ls_idx fc_idx goal in
    let w1 = World.get_fresh () in
    let w2 = World.get_fresh () in
    RWandR ((w, fprop), (w1, w2))
  | Comm (ls_idx, rc_idx) ->
    let w = Seq.get_nth_w ls_idx goal in
    let (w1,w2,_) = Seq.get_nth_rc ls_idx rc_idx goal in
    RComm (w, (w1,w2))
  | ZeroU ls_idx ->
    let w = Seq.get_nth_w ls_idx goal in
    let w' = World.get_fresh () in
    let rename = Seq.make_rename goal in
    RZeroU (w, (w', rename))
  | ZeroD (w_idx, w1_idx) ->
    let w = Seq.get_nth_w w_idx goal in
    let w1 = Seq.get_nth_w w1_idx goal in
    let _, w2,_ = Seq.find_nth_rc w_idx (fun (wl,_,_) -> World.eq wl w1) goal in
    let rename = Seq.make_rename ~rule:(fun w' -> if World.eq w' w1 then w else World.get_fresh ()) goal in
    RZeroD (w, (w1,w2), rename)
  | StarR (ls_idx, rc_idx, fc_idx) ->
    let w = Seq.get_nth_w ls_idx goal in
    let w1,w2,_ = Seq.get_nth_rc ls_idx rc_idx goal in
    let fprop = Seq.get_nth_fc ls_idx fc_idx goal in
    RStarR (w, (w1,w2), fprop)
  | WandL (w_idx, tc_idx, w1_idx) -> 
    let w = Seq.get_nth_w w_idx goal in
    let w1 = Seq.get_nth_w w1_idx goal in
    let w2 = Seq.find_parent (w, w1) goal in
    let tprop = Seq.get_nth_tc w_idx tc_idx goal in
    RWandL (w2, (w, w1), tprop)
  | Assoc (w1_idx, w2_idx, w3_idx) ->
    let w1 = Seq.get_nth_w w1_idx goal in
    let w2 = Seq.get_nth_w w2_idx goal in
    let w3 = Seq.get_nth_w w3_idx goal in
    let w' = Seq.find_parent (w1,w2) goal in
      let w = Seq.find_parent (w', w3) goal in
      let w'' = World.get_fresh () in
      let rename1 = Seq.make_rename goal in
      let rename2 = Seq.make_rename goal in
      let rename3 = Seq.make_rename goal in
      RAssoc ((w, w', w1, w2, w3), (w'', rename1, rename2, rename3))
  with
  | Not_found -> failwith "rule_to_inter_rule: invalid index"
  | Failure msg -> failwith ("rule_to_inter_rule: " ^ msg)

                   
let inter_rule_to_rule goal r = 
  try 
    match r with
    | RInit (w, tc_prop, fc_prop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let tc_idx = Seq.get_tc_idx goal ls_idx tc_prop in
      let fc_idx = Seq.get_fc_idx goal ls_idx fc_prop in
      Init (ls_idx, tc_idx, fc_idx)
    | RTopR (w, fprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let fc_idx = Seq.get_fc_idx goal ls_idx fprop in
      TopR (ls_idx, fc_idx)
    | RBotL (w, tprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let tc_idx = Seq.get_tc_idx goal ls_idx tprop in
      BotL (ls_idx, tc_idx)
    | RUnitR (w, fprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let fc_idx = Seq.get_fc_idx goal ls_idx fprop in
      UnitR (ls_idx, fc_idx)
    | RNegL (w, tprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let tc_idx = Seq.get_tc_idx goal ls_idx tprop in
      NegL (ls_idx, tc_idx)
    | RNegR (w, fprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let fc_idx = Seq.get_fc_idx goal ls_idx fprop in
      NegR (ls_idx, fc_idx)
    | RAndL (w, tprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let tc_idx = Seq.get_tc_idx goal ls_idx tprop in
      AndL (ls_idx, tc_idx)
    | RAndR (w, fprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let fc_idx = Seq.get_fc_idx goal ls_idx fprop in
      AndR (ls_idx, fc_idx)
    | ROrL (w, tprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let tc_idx = Seq.get_tc_idx goal ls_idx tprop in
      OrL (ls_idx, tc_idx)
    | ROrR (w, fprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let fc_idx = Seq.get_fc_idx goal ls_idx fprop in
      OrR (ls_idx, fc_idx)
    | RImplyL (w, tprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let tc_idx = Seq.get_tc_idx goal ls_idx tprop in
      ImplyL (ls_idx, tc_idx)
    | RImplyR (w, fprop) -> 
      let ls_idx = Seq.get_ls_idx goal w in
      let fc_idx = Seq.get_fc_idx goal ls_idx fprop in
      ImplyR (ls_idx, fc_idx)
    | RUnitL (w, tprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let tc_idx = Seq.get_tc_idx goal ls_idx tprop in
      UnitL (ls_idx, tc_idx)
    | RStarL ((w, tprop), (w1, w2)) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let tc_idx = Seq.get_tc_idx goal ls_idx tprop in
      StarL (ls_idx, tc_idx)
    | RWandR ((w, fprop), (w1, w2)) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let fc_idx = Seq.get_fc_idx goal ls_idx fprop in
      WandR (ls_idx, fc_idx)
    | RComm (w, com) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let rc_idx = Seq.get_rc_idx goal ls_idx com in
      Comm (ls_idx, rc_idx)
    | RZeroU (w, (w', rename)) ->
      let ls_idx = Seq.get_ls_idx goal w in
      ZeroU ls_idx
    | RZeroD (w, (w1,w2), rename) ->
      let w_idx = Seq.get_ls_idx goal w in
      let w1_idx = Seq.get_ls_idx goal w1 in
      ZeroD (w_idx, w1_idx)
    | RStarR (w, com, fprop) ->
      let ls_idx = Seq.get_ls_idx goal w in
      let rc_idx = Seq.get_rc_idx goal ls_idx com in
      let fc_idx = Seq.get_fc_idx goal ls_idx fprop in
      StarR (ls_idx, rc_idx, fc_idx)  
    | RWandL (w2, (w, w1), tprop) ->
      let w_idx = Seq.get_ls_idx goal w in
      let w1_idx = Seq.get_ls_idx goal w1 in
      let tc_idx = Seq.get_tc_idx goal w_idx tprop in
      WandL (w_idx, tc_idx, w1_idx)
    | RAssoc ((_, _, w1, w2, w3), _) ->
      let w1_idx = Seq.get_ls_idx goal w1 in
      let w2_idx = Seq.get_ls_idx goal w2 in
      let w3_idx = Seq.get_ls_idx goal w3 in
      Assoc (w1_idx, w2_idx, w3_idx)
  with
  | Not_found -> failwith "inter_rule_to_rule: invalid index"
  | Failure msg -> failwith ("inter_rule_to_rule: " ^ msg)


(* Pretty printer *)
let pr_goal = Seq.to_string

let i_one_str i1 = "(" ^ string_of_int i1 ^ ")"
let i_pair_str (i1, i2) = "(" ^ string_of_int i1 ^ ", " ^ string_of_int i2 ^ ")"
let i_triple_str (i1, i2, i3) = "(" ^ string_of_int i1 ^ ", " ^ string_of_int i2 ^ ", " ^ string_of_int i3 ^ ")"

let pr_rule = function
  | Init triple -> "Init" ^ (i_triple_str triple)
  | TopR tuple -> "TopR" ^ (i_pair_str tuple)
  | BotL tuple -> "BotL" ^ (i_pair_str tuple)
  | NegL tuple -> "NegL" ^ (i_pair_str tuple)
  | NegR tuple -> "NegR" ^ (i_pair_str tuple)
  | AndL tuple -> "AndL" ^ (i_pair_str tuple)
  | AndR tuple -> "AndR" ^ (i_pair_str tuple)
  | OrL tuple -> "OrL" ^ (i_pair_str tuple)
  | OrR tuple -> "OrR" ^ (i_pair_str tuple)
  | ImplyL tuple -> "ImplyL" ^ (i_pair_str tuple)
  | ImplyR tuple -> "ImplyR" ^ (i_pair_str tuple)
  | UnitL tuple -> "UnitL" ^ (i_pair_str tuple)
  | UnitR tuple -> "UnitR" ^ (i_pair_str tuple)
  | StarL tuple -> "StarL" ^ (i_pair_str tuple)
  | WandR tuple -> "WandR" ^ (i_pair_str tuple)
  | Comm tuple -> "Comm" ^ (i_pair_str tuple)
  | ZeroU one -> "ZeroU" ^ (i_one_str one)
  | ZeroD tuple -> "ZeroD" ^ (i_pair_str tuple)
  | StarR triple -> "StarR" ^ (i_triple_str triple)
  | WandL triple -> "WandL" ^ (i_triple_str triple)
  | Assoc triple -> "Assoc" ^ (i_triple_str triple)

let pr_inter_rule = function
  | RInit _ -> "Init"
  | RTopR _ -> "TopR"
  | RBotL _ -> "BotL"
  | RNegL _ -> "NegL"
  | RNegR _ -> "NegR"
  | RAndL _ -> "AndL"
  | RAndR _ -> "AndR"
  | ROrL _ -> "OrL"
  | ROrR _ -> "OrR"
  | RImplyL _ -> "ImplyL"
  | RImplyR _ -> "ImplyR"
  | RUnitL _ -> "UnitL"
  | RUnitR _ -> "UnitR"
  | RStarL _ -> "StarL"
  | RWandR _ -> "WandR"
  | RComm (w, (wr, wl)) -> "Comm (" ^ World.to_string w ^ ", " ^  World.to_string wr ^ ", " ^  World.to_string wl ^ ")"
  | RZeroU _ -> "ZeroU"
  | RZeroD _ -> "ZeroD"
  | RStarR _ -> "StarR"
  | RWandL _ -> "WandL"
  | RAssoc ((w, w', w1, w2, w3),_) -> 
    "Assoc (" ^ World.to_string w ^ ", " ^  World.to_string w' ^
      ", " ^  World.to_string w1 ^ ", " ^  World.to_string w2 ^ ", " ^  World.to_string w3 ^ ")"

let rec pr_proof_tree ?(show_hidden=false) {open_subgoals; goal; ref} =
  match ref with
  | None -> pr_goal ~show_hidden goal
  | Some (irule, ptl) ->
    pr_goal goal ^ "\n" ^
    "BY " ^ pr_inter_rule irule ^ "\n" ^
      (List.fold_left ptl ~init:"\n" ~f:(fun aux pt -> aux ^ pr_proof_tree ~show_hidden pt))

let rec pr_proof_tree_rules indent {open_subgoals; goal; ref} =
  match ref with
  | None -> indent ^ "...ing...\n"
  | Some (irule, []) ->
    let rule = inter_rule_to_rule goal irule in
    indent ^ "BY " ^ pr_rule rule ^ " LEAF\n"
  | Some (irule, ptl) ->
    let rule = inter_rule_to_rule goal irule in
    indent ^ "BY " ^ pr_rule rule ^ "\n" ^
      (List.fold_left ptl ~init:"" ~f:(fun aux pt -> aux ^ pr_proof_tree_rules (indent ^ " ") pt))


let pr_proof_tree_rules = pr_proof_tree_rules ""

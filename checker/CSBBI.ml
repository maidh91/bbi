(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

module Rule =
struct
  let id = "CSBBI"

  type seq = WSeq.t
  with sexp

  type premise =
  | PUnit
  | POne of seq
  | PTwo of seq * seq
  with sexp

  (** Extraction functions for premise  *)
  let match_prem_fails (expected : string) (given_prem : premise) =
    String.concat ["A premise of the form "; expected; " is expected, ";
                   "but "; sexp_of_premise given_prem |! Sexp.to_string_hum; " is given."]
    |! wrap_err

  let match_prem_unit = function
    | PUnit -> wrap ()
    | prem -> match_prem_fails "POne W" prem
        
  let match_prem_one = function
    | POne wseq -> wrap wseq
    | prem -> match_prem_fails "POne W" prem

  let match_prem_two = function
    | PTwo (wseq_1, wseq_2) -> wrap (wseq_1, wseq_2)
    | prem -> match_prem_fails "PTwo (W_1, W_2)" prem

  let match_prem_unit_exn prem = match_prem_unit prem |! simpl_unwrap
  let match_prem_one_exn prem = match_prem_one prem |! simpl_unwrap
  let match_prem_two_exn prem = match_prem_two prem |! simpl_unwrap

  type t =
  | Init of Prop.t 
  | TopR
  | BotL
  | NegL of Prop.t 
  | NegR of Prop.t 
  | AndL of Prop.t 
  | AndR of Prop.t 
  | OrL of Prop.t 
  | OrR of Prop.t 
  | ImplyL of Prop.t 
  | ImplyR of Prop.t 
  | UnitL
  | UnitR
  | StarL of Prop.t * (World.t * World.t)
  | StarR of ((World.t * World.t) * Prop.t) 
  | WandL of ((World.t * World.t) * Prop.t) 
  | WandR of Prop.t * (World.t * World.t)
  | TC of (World.t * World.t) 
  | TP of (World.t * World.t) 
  | Comm of (World.t * World.t) 
  | Assoc of ((World.t * World.t) * (World.t * World.t)) * (World.t * World.rename * World.rename * World.rename)
  | ZeroU of unit * (World.rename * World.t)
  | ZeroD of (World.t * World.t) * World.rename
  with sexp

  let valid_seq = WSeq.syntactic_well_formed

  let mpair_with_worlds w_A w_B = function
    | WSeq.Mpair (wseq_A, wseq_B) -> 
      World.eq w_A wseq_A.WSeq.world && World.eq w_B wseq_B.WSeq.world
    | _ -> false

  let apair_with_worlds w_A w_B = function
    | WSeq.Apair (wseq_A, wseq_B) -> 
      World.eq w_A wseq_A.WSeq.world && World.eq w_B wseq_B.WSeq.world
    | _ -> false

  let apair_with_sibling w_s = function
    | WSeq.Apair (wseq_s, _) -> 
      World.eq w_s wseq_s.WSeq.world 
    | _ -> false

  let mpair_with_rchild w_r = function
    | WSeq.Mpair (_, wseq_r) -> 
      World.eq w_r wseq_r.WSeq.world
    | _ -> false

  let ext_ws_mpair = function
    | WSeq.Mpair (wseq_A, wseq_B) -> wrap (wseq_A, wseq_B)
    | _ -> 
      String.concat ["A world state of the form W, W is expected, ";
                     "but a given world state is of the form W<W>."]
      |! wrap_err

  let ext_ws_apair = function
    | WSeq.Apair (wseq_A, wseq_B) -> wrap (wseq_A, wseq_B)
    | _ -> 
      String.concat ["A world state of the form W<W> is expected, ";
                     "but a given world state is of the form W, W."]
      |! wrap_err

  let ext_ws_mpair_exn ws = ext_ws_mpair ws |! simpl_unwrap
  let ext_ws_apair_exn ws = ext_ws_apair ws |! simpl_unwrap

  (** Auxililary functions for the forward function *)
  let forward_fails case prem =
    String.concat [Error.fails case; "\n";
                   "The following premise is given:"; "\n";
                   sexp_of_premise prem |! Sexp.to_string_hum]

  (* forward_neg_left_exn : Prop.t(info) -> premise -> Seq.t 
     forward_neg_left_exn !A (\Gamma => \Delta; A) returns (\Gamma; !A => \Delta). *)
  let forward_neg_left_exn prop prem =
    try
      let prop_A = Prop.match_prop_neg_exn prop in
      let wseq = match_prem_one_exn prem in
      WSeq.add_tc_prop_exn (Prop.Neg prop_A) wseq 
      |! WSeq.remove_fc_exn prop_A 
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_neg_left" prem) e

  let forward_neg_right_exn prop prem =
    try
      let prop_A = Prop.match_prop_neg_exn prop in
      let wseq = match_prem_one_exn prem in
      WSeq.add_fc_exn (Prop.Neg prop_A) wseq 
      |! WSeq.remove_tc_prop_exn prop_A 
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_neg_right" prem) e

  let forward_and_left_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_and_exn prop in
      let wseq = match_prem_one_exn prem in
      WSeq.add_tc_prop_exn (Prop.And (prop_A, prop_B)) wseq 
      |! WSeq.remove_tc_prop prop_A 
      |! unwrap "Can't remove the proposition A."
      |! WSeq.remove_tc_prop prop_B
      |! unwrap "Can't remove the proposition B."
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_and_left" prem) e

  (* forward_and_right_exn : Prop.t(info) -> premise -> Seq.t
     forward_and_right_exn (A /\ B) ((\Gamma_1 => \Delta_1; A), (\Gamma_2 => \Delta_2; B)) 
     returns (\Gamma_1 => \Delta_1; A /\ B) *)
  let forward_and_right_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_and_exn prop in
      let wseq_1, _ = match_prem_two_exn prem in
      WSeq.add_fc_exn (Prop.And (prop_A, prop_B)) wseq_1
      |! WSeq.remove_fc_exn prop_A
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_and_right" prem) e

  let forward_or_left_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_or prop |! simpl_unwrap in
      let wseq_1, _ = match_prem_two prem |! simpl_unwrap in
      WSeq.add_tc_prop_exn (Prop.Or (prop_A, prop_B)) wseq_1
      |! WSeq.remove_tc_prop_exn prop_A
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_or_left" prem) e

  let forward_or_right_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_or prop |! simpl_unwrap in
      let wseq = match_prem_one prem |! simpl_unwrap in
      WSeq.add_fc_exn (Prop.Or (prop_A, prop_B)) wseq 
      |! WSeq.remove_fc prop_A 
      |! unwrap "Can't remove the proposition A."
      (* |! (fun wseq -> WSeq.sexp_of_t wseq |! Sexp.to_string_hum |! print_string |! print_newline; wseq) *)
      |! WSeq.remove_fc prop_B
      |! unwrap "Can't remove the proposition B."
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_or_right" prem) e

  let forward_imply_left_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_imply prop |! simpl_unwrap in
      let wseq_1, _ = match_prem_two prem |! simpl_unwrap in
      WSeq.add_tc_prop_exn (Prop.Imply (prop_A, prop_B)) wseq_1
      |! WSeq.remove_fc_exn prop_A
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_imply_left" prem) e

  let forward_imply_right_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_imply prop |! simpl_unwrap in
      let wseq = match_prem_one prem |! simpl_unwrap in
      WSeq.add_fc_exn (Prop.Imply (prop_A, prop_B)) wseq 
      |! WSeq.remove_tc_prop prop_A 
      |! unwrap "Can't remove the proposition A."
      |! WSeq.remove_fc prop_B
      |! unwrap "Can't remove the proposition B."
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_imply_right" prem) e

  let forward_unit_left_exn prem =
    try
      let wseq = match_prem_one prem |! simpl_unwrap in
      WSeq.add_tc_prop_exn Prop.Unit wseq 
      |! WSeq.remove_tc_mzero_exn    
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_unit_left" prem) e

  let forward_star_left_exn (prop, (w_A, w_B)) prem =
    try
      let prop_A, prop_B = Prop.match_prop_star prop |! simpl_unwrap in
      let wseq = match_prem_one prem |! simpl_unwrap in
      let _, wseq_r = WSeq.pick_wc_exn (mpair_with_worlds w_A w_B) wseq in
      WSeq.add_tc_prop_exn (Prop.Star (prop_A, prop_B)) wseq_r
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_star_left" prem) e

  let forward_star_right_exn ((w_A, w_B), prop) prem =
    try
      let prop_A, prop_B = Prop.match_prop_star prop |! simpl_unwrap in
      let wseq_A, wseq_B = match_prem_two prem |! simpl_unwrap in
      let (wseq_l, wseq_r), wseq = WSeq.pick_wc_exn (mpair_with_worlds w_A w_B) wseq_A
                                   |! Tuple.T2.map1 ~f:ext_ws_mpair_exn in
      let wseq_l' = WSeq.remove_fc_exn prop_A wseq_l in
      WSeq.add_wc_mpair_exn (wseq_l', wseq_r) wseq
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_star_right" prem) e
        
  let forward_wand_left_exn ((w_A, w_B), prop) prem =
    try
      let prop_A, prop_B = Prop.match_prop_wand prop |! simpl_unwrap in
      let wseq_A, wseq_B = match_prem_two prem |! simpl_unwrap in
      let (wseq_left, wseq_right), wseq_r = 
        WSeq.pick_wc_exn (apair_with_worlds w_A w_B) wseq_A 
        |! Tuple.T2.map1 ~f:ext_ws_apair_exn in
      let wseq_left' = WSeq.remove_fc_exn prop_A wseq_left in
      WSeq.add_wc_apair_exn (wseq_left', wseq_right) wseq_r
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_wand_left" prem) e

  let forward_wand_right_exn (prop, (w_A, w_B)) prem =
    try
      let prop_A, prop_B = Prop.match_prop_wand prop |! simpl_unwrap in
      let wseq = match_prem_one prem |! simpl_unwrap in
      let _, wseq_r = WSeq.pick_wc_exn (apair_with_worlds w_A w_B) wseq in
      WSeq.add_fc_exn (Prop.Wand (prop_A, prop_B)) wseq_r
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_wand_right" prem) e

  let forward_tc_exn (w_c1, w_c2) prem =
    try
      let wseq = match_prem_one prem |! simpl_unwrap in
      let (wseq_c2, wseq'), wseq_c1 = 
        WSeq.pick_wc (apair_with_sibling w_c2) wseq 
        |! simpl_unwrap 
        |! Tuple.T2.map1 ~f:ext_ws_apair_exn (* This operation must success *) in
      WSeq.add_wc_mpair_exn (wseq_c1, wseq_c2) wseq'
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_tc" prem) e

  let forward_tp_exn (w_s, w_p) prem =
    try
      let wseq = match_prem_one prem |! simpl_unwrap in
      let (wseq', wseq_s), wseq_p =
        WSeq.pick_wc_exn (mpair_with_rchild w_s) wseq
        |! Tuple.T2.map1 ~f:ext_ws_mpair_exn in
      WSeq.add_wc_apair_exn (wseq_s, wseq_p) wseq'
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_tp" prem) e

  let forward_comm_exn (w_l, w_r) prem =
    try
      let wseq = match_prem_one prem |! simpl_unwrap in
      let (wseq_r, wseq_l), wseq' =
        WSeq.pick_wc_exn (mpair_with_worlds w_r w_l) wseq        
        |! Tuple.T2.map1 ~f:ext_ws_mpair_exn in
      WSeq.add_wc_mpair_exn (wseq_l, wseq_r) wseq'
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_comm" prem) e

  let forward_assoc_exn (((w', w_3), (w_1, w_2)), (w_n, rn_1, rn_2, rn_3)) prem =
    try
      let wseq = match_prem_one_exn prem in
      WSeq.pick_wc_exn (mpair_with_worlds (World.rename_exn rn_1 w_1) w_n) wseq |! snd     
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_assoc" prem) e

  let forward_zero_up_exn (rn, w_e) prem =
    try
      let { WSeq.world = w; } as wseq = match_prem_one prem |! simpl_unwrap in
      WSeq.pick_wc_exn (mpair_with_worlds (World.rename_exn rn w) w_e) wseq |! snd
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_zero_up" prem) e

  let remove_tc s wseq =
    match s with
    | WSeq.Prop prop -> WSeq.remove_tc_prop prop wseq
    | WSeq.Mzero -> WSeq.remove_tc_mzero wseq
  let remove_tc_exn s wseq = remove_tc s wseq |! simpl_unwrap

  let forward_zero_down_exn ((w_c1, w_c2), rn) prem =
    try
      let { WSeq.world = w } as wseq = match_prem_one_exn prem in
      let { WSeq.tcontext = tc_c1; WSeq.fcontext = fc_c1; WSeq.wcontext = wc_c1; }, wseq_c2_ =
        WSeq.pick_wc_exn (mpair_with_worlds w_c1 w_c2) wseq
        |! Tuple.T2.map1 ~f:ext_ws_mpair_exn 
        |! fst in
      let f wseq ws =
        match ws with
        | WSeq.Mpair ({ WSeq.world = w_1 }, { WSeq.world = w_2 }) -> 
          WSeq.remove_wc_mpair (World.rename_exn rn w_1, World.rename_exn rn w_2) wseq |! simpl_unwrap
        | WSeq.Apair ({ WSeq.world = w_1 }, { WSeq.world = w_2 }) -> 
          WSeq.remove_wc_apair (World.rename_exn rn w_1, World.rename_exn rn w_2) wseq |! simpl_unwrap in            
      WSeq.remove_wc_apair_exn (World.rename_exn rn w_c2, World.rename_exn rn w) wseq 
      |! (fun wseq -> List.fold_left tc_c1 ~init:wseq ~f:(Fn.flip remove_tc_exn))
      |! (fun wseq -> List.fold_left fc_c1 ~init:wseq ~f:(Fn.flip WSeq.remove_fc_exn))
      |! (fun wseq -> List.fold_left wc_c1 ~init:wseq ~f:f)
    with e -> exn_reraise ~msg:(forward_fails "CSBBI.forward_zero_up" prem) e

  (* forward : t -> premise -> seq result
     Invaraint : if forward r p returns W, then backward W r should return p. *)
  let forward rule prem = 
    try
      let seq =
        match rule with
        | Init _ -> raise NotImplemented
        | TopR -> raise NotImplemented
        | BotL -> raise NotImplemented
        | NegL prop -> forward_neg_left_exn prop prem 
        | NegR prop -> forward_neg_right_exn prop prem 
        | AndL prop -> forward_and_left_exn prop prem 
        | AndR prop -> forward_and_right_exn prop prem
        | OrL prop -> forward_or_left_exn prop prem
        | OrR prop -> forward_or_right_exn prop prem
        | ImplyL prop -> forward_imply_left_exn prop prem
        | ImplyR prop -> forward_imply_right_exn prop prem
        | UnitL -> forward_unit_left_exn prem
        | UnitR -> raise NotImplemented
        | StarL (prop, worlds) -> forward_star_left_exn (prop, worlds) prem
        | StarR (worlds, prop) -> forward_star_right_exn (worlds, prop) prem
        | WandL (worlds, prop) -> forward_wand_left_exn (worlds, prop) prem
        | WandR (prop, worlds) -> forward_wand_right_exn (prop, worlds) prem
        | TC worlds -> forward_tc_exn worlds prem
        | TP worlds -> forward_tp_exn worlds prem
        | Comm worlds -> forward_comm_exn worlds prem
        | Assoc (rels, worlds) -> forward_assoc_exn (rels, worlds) prem
        | ZeroU ((), info) -> forward_zero_up_exn info prem
        | ZeroD (worlds, rn) -> forward_zero_down_exn (worlds, rn) prem
      in wrap seq
    with e -> exn_wrap_err ~msg:(Error.fails "CSBBI.forward") e

  let pick_wc_mpair (w1,w2) seq = 
    let get_mpair = function 
      | WSeq.Mpair(wl, wr) -> World.eq w1 wl.WSeq.world && World.eq w2 wr.WSeq.world 
      | _ -> false in
    try
      match WSeq.pick_wc get_mpair seq |! simpl_unwrap with
      | WSeq.Mpair (t1,t2), remain -> wrap ((t1,t2), remain)
      | _ -> wrap_err "Impossible return value"
    with
    | e -> exn_wrap_err ~msg:("pick_wc_mpair failed") e

  let pick_wc_apair (w1,w2) seq = 
    let get_apair = function 
      | WSeq.Apair (wl, wr) -> World.eq w1 wl.WSeq.world && World.eq w2 wr.WSeq.world 
      | _ -> false in
    try
      match WSeq.pick_wc get_apair seq |! simpl_unwrap with
      | WSeq.Apair (t1,t2), remain -> wrap ((t1,t2), remain)
      | _ -> wrap_err "Impossible return value"
    with
    | e -> exn_wrap_err ~msg:("pick_wc_apair failed") e

  let wrap_p_one seq = wrap (POne seq)
  let wrap_p_two (seq1, seq2) = wrap (PTwo (seq1, seq2))
    
  let backward rule seq = 
    try begin
      match rule with
      | Init (prop) -> 
        WSeq.exists_tc_prop prop seq |! simpl_unwrap;
        WSeq.exists_fc prop seq |! simpl_unwrap;
        wrap PUnit
          
      | TopR -> 
        WSeq.exists_fc Prop.Top seq |! simpl_unwrap;
        wrap PUnit

      | BotL -> 
        WSeq.exists_tc_prop Prop.Bot seq |! simpl_unwrap;
        wrap PUnit

      | NegL (Prop.Neg prop as neg_prop) -> 
        seq
        |! WSeq.remove_tc_prop neg_prop
          >> WSeq.add_fc prop
          >> wrap_p_one

      | NegR (Prop.Neg prop as neg_prop) -> 
        seq
        |! WSeq.remove_fc neg_prop
          >> WSeq.add_tc_prop prop
          >> wrap_p_one

      | AndL (Prop.And (prop_a, prop_b) as and_prop) -> 
        seq
        |! WSeq.remove_tc_prop and_prop
          >> WSeq.add_tc_prop prop_a 
          >> WSeq.add_tc_prop prop_b
          >> wrap_p_one

      | AndR (Prop.And (prop_a, prop_b) as and_prop) -> 
        let base_seq = seq |! WSeq.remove_fc and_prop |! simpl_unwrap in
        (base_seq
         |! WSeq.add_fc prop_a
         |! unwrap "Add prop_A failed", (* unlikely failed *)
         base_seq
         |! WSeq.add_fc prop_b
         |! unwrap "Add prop_B failed") (* unlikely failed *)
        |! wrap_p_two

      | OrL (Prop.Or (prop_a, prop_b) as or_prop) -> 
        let base_seq = seq |! WSeq.remove_tc_prop or_prop |! simpl_unwrap in
        (base_seq
         |! WSeq.add_tc_prop prop_a
         |! unwrap "Add prop_A failed",
         base_seq
         |! WSeq.add_tc_prop prop_b
         |! unwrap "Add prop_B failed")
        |! wrap_p_two

      | OrR (Prop.Or (prop_a, prop_b) as or_prop) -> 
        seq 
        |! WSeq.remove_fc or_prop
          >> WSeq.add_fc prop_a
          >> WSeq.add_fc prop_b
          >> wrap_p_one

      | ImplyL (Prop.Imply (prop_a, prop_b) as imply_prop) -> 
        let base_seq_result = seq |! WSeq.remove_tc_prop imply_prop in
        (base_seq_result
         >> WSeq.add_fc prop_a,
         base_seq_result
         >> WSeq.add_tc_prop prop_b)
        |! merge_result_pair
          >> wrap_p_two

      | ImplyR (Prop.Imply (prop_a, prop_b) as imply_prop) -> 
        seq 
        |! WSeq.remove_fc imply_prop
          >> WSeq.add_tc_prop prop_a
          >> WSeq.add_fc prop_b
          >> wrap_p_one

      | UnitL -> 
        seq 
        |! WSeq.remove_tc_prop (Prop.Unit)
          >> WSeq.add_tc_mzero
          >> wrap_p_one

      | UnitR -> 
        WSeq.exists_tc_mzero seq |! simpl_unwrap;
        WSeq.exists_fc Prop.Unit seq |! simpl_unwrap;
        wrap PUnit

      | StarL ((Prop.Star (prop_a, prop_b) as star_prop), (w1, w2)) ->
        seq 
        |! WSeq.remove_tc_prop star_prop
          >> WSeq.add_wc_mpair (WSeq.create ~tc:[WSeq.Prop prop_a] w1, WSeq.create ~tc:[WSeq.Prop prop_b] w2)
          >> wrap_p_one

      | StarR (wc_mpair, (Prop.Star (prop_a, prop_b) as star_prop)) ->
        WSeq.exists_fc star_prop seq |! simpl_unwrap;
        let (wl, wr), base_seq  = WSeq.pick_wc_mpair wc_mpair seq |! simpl_unwrap in
        let wl_mod = wl |! WSeq.add_fc prop_a |! unwrap "Add A failed"  in
        let wr_mod = wr |! WSeq.add_fc prop_b |! unwrap "Add b failed" in
        (base_seq
         |! WSeq.add_wc_mpair (wl_mod, wr),
         base_seq
         |! WSeq.add_wc_mpair (wl, wr_mod))
        |! merge_result_pair
          >> wrap_p_two
            
      | WandL (wc_apair, (Prop.Wand (prop_a, prop_b) as wand_prop)) ->
        WSeq.exists_tc_prop wand_prop seq |! simpl_unwrap;
        let (wl, wr), base_seq  = WSeq.pick_wc_apair wc_apair seq |! simpl_unwrap in
        let wl_mod = wl |! WSeq.add_fc prop_a |! unwrap "Add A failed"  in
        let wr_mod = wr |! WSeq.add_tc_prop prop_b |! unwrap "Add b failed" in
        (base_seq 
         |! WSeq.add_wc_apair (wl_mod, wr),
         base_seq
         |! WSeq.add_wc_apair (wl, wr_mod))
        |! merge_result_pair
          >> wrap_p_two

      | WandR ((Prop.Wand (prop_a, prop_b) as wand_prop), (w1, w2)) ->
        seq 
        |! WSeq.remove_fc wand_prop
          >> WSeq.add_wc_apair (WSeq.create ~tc:[WSeq.Prop prop_a] w1, WSeq.create ~fc:[prop_b] w2)
          >> wrap_p_one

      | TC wc_mpair ->
        let (wl, wr), base_seq  = WSeq.pick_wc_mpair wc_mpair seq |! simpl_unwrap in
        wl
        |! WSeq.add_wc_apair (wr, base_seq)
          >> wrap_p_one
        
      | TP wc_apair ->
        let (wl, wr), base_seq  = WSeq.pick_wc_apair wc_apair seq |! simpl_unwrap in
        wr
        |! WSeq.add_wc_mpair (base_seq, wl)
          >> wrap_p_one

      | Comm wc_mpair ->
        let (wl, wr), base_seq  = WSeq.pick_wc_mpair wc_mpair seq |! simpl_unwrap in
        base_seq
        |! WSeq.add_wc_mpair (wr, wl) 
          >> wrap_p_one

      | Assoc ((outer, inner), (w_new, rename1, rename2, rename3)) ->
        let (w', w3), base_seq  = WSeq.pick_wc_mpair outer seq |! unwrap "Cannot find outer" in
        let (w1, w2), w'_base_seq  = WSeq.pick_wc_mpair inner w' |! unwrap "Cannot find inner" in
        (* (\* Renamings are valid? *\) *)
        (* let worlds = WSeq.collect_world_names seq in *)
        (* worlds *)
        (* |! eq_list (Map.keys rename1) *)
        (* |! unwrap "rename1's domain <> worlds"; *)
        (* worlds *)
        (* |! eq_list (Map.keys rename2) *)
        (* |! unwrap "rename2's domain <> worlds"; *)
        (* worlds *)
        (* |! eq_list (Map.keys rename3) *)
        (* |! unwrap "rename3's domain <> worlds"; *)
        (* worlds *)
        (* |! List.rev_append (Map.data rename1) *)
        (* |! List.rev_append (Map.data rename2) *)
        (* |! List.rev_append (Map.data rename3) *)
        (* |! List.exn_if_dup ~compare:World.compare ~context:"Renamings' results are not distinct." ~to_sexp:World.sexp_of_t; *)
        (* Convert! *)
        let w1_new = 
          w1
          |! WSeq.add_wc_apair 
              (w2, (w'_base_seq 
                    |! WSeq.add_wc_apair (w3, base_seq) 
                    |! simpl_unwrap)) 
            >> WSeq.apply_rename rename1
          |! unwrap "Rename W1' failed" in
        let w2_new = 
          w2
          |! WSeq.add_wc_apair 
              (w1, (w'_base_seq 
                    |! WSeq.add_wc_apair (w3, base_seq) 
                    |! simpl_unwrap)) 
            >> WSeq.apply_rename rename2
          |! unwrap "Rename W2' failed" in
        let w3_new = 
          w3
          |! WSeq.add_wc_apair 
              ((w'_base_seq 
                     |! WSeq.add_wc_mpair (w1, w2) 
                     |! simpl_unwrap), base_seq) 
            >> WSeq.apply_rename rename3
          |! unwrap "Rename W3' failed" in
        seq
        |! WSeq.add_wc_mpair (w1_new, WSeq.create ~wc:[WSeq.Mpair(w2_new, w3_new)] w_new)
          >> wrap_p_one

      | ZeroU (_, (rename, w'')) ->
        (* (\* Renamings are valid? *\) *)
        (* let worlds = WSeq.collect_world_names seq in *)
        (* worlds *)
        (* |! eq_list (Map.keys rename) *)
        (* |! unwrap "rename's domain <> worlds"; *)
        (* worlds *)
        (* |! List.rev_append (Map.data rename) *)
        (* |! List.exn_if_dup ~compare:World.compare ~context:"Renaming's domain & range are not distinct."  ~to_sexp:World.sexp_of_t; *)
        (* Convert! *)
        let seq1 = WSeq.apply_rename rename seq |! simpl_unwrap in
        seq
        |! WSeq.add_wc_mpair (seq1, WSeq.create ~tc:[WSeq.Mzero] w'')
          >> wrap_p_one

      | ZeroD (wc_mpair, rename) ->
        let (wl, wr), base_seq  = WSeq.pick_wc_mpair wc_mpair seq |! simpl_unwrap in
        WSeq.exists_tc_mzero wr |! unwrap "wr is not mzero";
        (* Renamings are valid? *)
        (* let worlds = WSeq.collect_world_names seq in *)
        (* let rename_dump = "Rename:[" ^ World.rename_to_string rename  ^ "]" in *)
        (* worlds *)
        (* |! eq_list (Map.keys rename) *)
        (* |! unwrap "rename's domain <> worlds"; *)
        (* worlds *)
        (* |! List.rev_append (Map.data rename) *)
        (* |! List.exn_if_dup ~compare:World.compare ~context:("Renaming's domain & ranage are not distinct.\n" ^ rename_dump)  ~to_sexp:World.sexp_of_t; *)
        (* Convert! *)
        let wl_new = WSeq.apply_rename rename wl |! unwrap "wl rename failed" in
        let wr_new = WSeq.apply_rename rename wr |! unwrap "wr rename failed" in
        let base_seq_new = WSeq.apply_rename rename base_seq |! unwrap "base_seq rename failed" in
        let seq_with_s = seq |! WSeq.add_wc_apair (wr_new, base_seq_new) |! unwrap "seq_with_s failed" in
        WSeq.merge seq_with_s wl_new (* TODO: May make a problem. World name should be seq_with_s *)
        >> wrap_p_one
            
      | _ -> wrap_err "Invalid rule combination." |! simpl_unwrap
    end
    with
    | List.Duplicate_found (dup, msg) ->
      wrap_err ("Backward failed with " ^ (sexp_of_t rule |! Sexp.to_string_hum)
                ^ "\n" ^ msg 
                ^ "\nDuplicated found: "
                ^ (dup () |! Sexp.to_string_hum))
    | e -> exn_wrap_err ~msg:("Backward failed with " ^ (sexp_of_t rule |! Sexp.to_string_hum)) e


  let seq_eq = WSeq.eq

  let rule_to_tex_command = function
    | Init _ -> "\\RCSBinit"
    | TopR -> "\\RCSBtopright"
    | BotL -> "\\RCSBbotleft"
    | NegL _ -> "\\RCSBnegleft"
    | NegR _ -> "\\RCSBnegright"
    | AndL _ -> "\\RCSBandleft"
    | AndR _ -> "\\RCSBandright"
    | OrL _ -> "\\RCSBorleft"
    | OrR _ -> "\\RCSBorright"
    | ImplyL _ -> "\\RCSBimplyleft"
    | ImplyR _ -> "\\RCSBimplyright"
    | UnitL -> "\\RCSBunitleft"
    | UnitR -> "\\RCSBunitright"
    | StarL _ -> "\\RCSBstarleft"
    | StarR _ -> "\\RCSBstarright"
    | WandL _ -> "\\RCSBwandleft"
    | WandR _ -> "\\RCSBwandright"
    | TC _ -> "\\RCSBdown"
    | TP _ -> "\\RCSBup"
    | Comm _ -> "\\RCSBcomm"
    | Assoc _ -> "\\RCSBassoc"
    | ZeroU _ -> "\\RCSBmultzeroup"
    | ZeroD _ -> "\\RCSBmultzerodown"

  let no_highlight = fun _ -> false
  let tc_eq_prop prop1 wstate2 = WSeq.Prop prop1 = wstate2
  let tc_eq_mzero wstate2 = WSeq.Mzero = wstate2
  let fc_eq prop1 prop2 = prop1 = prop2

  let seq_to_tex = function
    | Init prop -> 
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop) 
        ~fc_highlight:(fc_eq prop) 
    | TopR ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq Prop.Top)
    | BotL ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop Prop.Bot)
        ~fc_highlight:no_highlight
    | NegL prop ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop)
        ~fc_highlight:no_highlight
    | NegR prop ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop)
    | AndL prop ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop)
        ~fc_highlight:no_highlight
    | AndR prop ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop)
    | OrL prop ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop)
        ~fc_highlight:no_highlight
    | OrR prop ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop)
    | ImplyL prop ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop)
        ~fc_highlight:no_highlight
    | ImplyR prop ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop)
    | UnitL ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop Prop.Unit)
        ~fc_highlight:no_highlight
    | UnitR ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:(tc_eq_mzero)
        ~fc_highlight:(fc_eq Prop.Unit)
    | StarL (prop, _) ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop)
        ~fc_highlight:no_highlight
    | StarR ((w1,w2), prop) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop)
    | WandL ((w1,w2), prop) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:(tc_eq_prop prop)
        ~fc_highlight:no_highlight
    | WandR (prop, _) ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop)
    | TC (w1,w2) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | TP (w1,w2) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | Comm (w1,w2) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | Assoc (((w1,_), (w2,_)), _) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | ZeroU _ ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | ZeroD ((w1,w2), _) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
end

module Proof = ProofFn (Rule)

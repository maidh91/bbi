(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

module CBuild = ProofBuilder.Make (CSBBI)

let ext_list_singleton = function
  | [e] -> wrap e
  | l -> wrap_err "A singleton list is expected, but a given list is not a singleton list."
    
(** Convert a L_BBI sequent into a corresponding CS_BBI proof *)
type elem = 
| Mpair of tree * tree
| Apair of tree * tree

and tree = World.t * elem list

let rec construct_tree rc w =
  match rc with
  | [] -> w, []
  | _ -> begin
    let rc_t, rc_f = List.partition rc 
      ~f:(fun { LSeq.parent = w_p; LSeq.lchild = w_l; LSeq.rchild = w_r } -> World.eq w w_p || World.eq w w_l || World.eq w w_r)  in
    let f ({ LSeq.parent = w_p; LSeq.lchild = w_l; LSeq.rchild = w_r}) =
      if World.eq w w_p then
        Mpair (construct_tree rc_f w_l, construct_tree rc_f w_r)
      else if World.eq w w_l then
        Apair (construct_tree rc_f w_r, construct_tree rc_f w_p)
      else
        Apair (construct_tree rc_f w_l, construct_tree rc_f w_p)
    in w, List.map ~f:f rc_t
  end

let rec convert_ws = function 
  | LSeq.Prop prop -> WSeq.Prop prop
  | LSeq.Mzero -> WSeq.Mzero

and convert_tc w tc = 
  List.filter ~f:(fun (_, w') -> World.eq w w') tc
  |! List.map ~f:(fun (ws, _) -> convert_ws ws) 

and convert_fc w fc = 
  List.filter ~f:(fun (_, w') -> World.eq w w') fc
  |! List.map ~f:(fun (prop, _) -> prop) 

and convert_s_wc tc fc  = function
  | Mpair (tree_l, tree_r) -> WSeq.Mpair (convert_s_seq tc fc tree_l, convert_s_seq tc fc tree_r)
  | Apair (tree_s, tree_p) -> WSeq.Apair (convert_s_seq tc fc tree_s, convert_s_seq tc fc tree_p)

and convert_s_seq tc fc (w, el) =
  { WSeq.world = w; 
    WSeq.tcontext = convert_tc w tc; 
    WSeq.fcontext = convert_fc w fc; 
    WSeq.wcontext = List.map ~f:(convert_s_wc tc fc) el; }
      
(* convert_s : World.t -> LSeq.t -> WSeq.t *)  
(* Assumption : a given labelled world sequent is well-formed *)
let convert_s_exn ref_w { LSeq.relations = rc; LSeq.tcontext = tc; LSeq.fcontext = fc; }  =
  try
    convert_s_seq tc fc (construct_tree rc ref_w)
  with e -> exn_reraise ~msg:(Error.fails "convert_s") e
    
(** Display *)
let rec worlds_ws = function
  | WSeq.Mpair (ws_1, ws_2) -> Set.union (worlds_seq ws_1) (worlds_seq ws_2)
  | WSeq.Apair (ws_1, ws_2) -> Set.union (worlds_seq ws_1) (worlds_seq ws_2)

and worlds_seq { WSeq.world = world; WSeq.wcontext = wc; } =
  List.map ~f:worlds_ws wc |! Set.union_list |! Fn.flip Set.add world

type t = Norm | Comm

let rec build_lm = function
  | [] -> Map.empty
  | { LSeq.parent = w_p; LSeq.lchild = w_l; LSeq.rchild = w_r; } :: rc ->
    build_lm rc 
    |! Map.add ~key:(w_l, w_r) ~data:Norm
    |! Map.add ~key:(w_r, w_l) ~data:Comm

let lookup_lm_exn lm w =
  try
    Map.find_exn lm w
  with Not_found -> exn_failure (Error.fails "lookup_lm")

let exists_rc_bool rel lseq = 
  try
    LSeq.exists_rc rel lseq |! simpl_unwrap; true
  with Failure _ -> false

let rec display_exn_comm_aux lm i (_, wseq, _ as cproof) =
  match List.nth wseq.WSeq.wcontext i with
  | Some ws -> begin
    match ws with
    | WSeq.Mpair ({ WSeq.world = w_1 }, { WSeq.world = w_2 }) -> begin
      match lookup_lm_exn lm (w_1, w_2) with
      | Norm -> display_exn_comm_aux lm (i + 1) cproof
      | Comm -> begin
        CBuild.construct_exn (CSBBI.Rule.Comm (w_2, w_1)) (CSBBI.Proof.POne cproof)
        |! display_exn_comm_aux lm 0
      end
    end
    | _ -> display_exn_comm_aux lm (i + 1) cproof
  end
  | None -> cproof

let display_exn_comm lm cproof = display_exn_comm_aux lm 0 cproof

let rec display_exn_aux lm ref_w cproof =
  let _, ({ WSeq.world = cur_w; WSeq.wcontext = wc } as wseq), _ as cproof' =
    cproof in
    (* display_exn_comm lm cproof in *)
  (* Case 1. ref_w is already the reference world of a given CS_BBI proof. *)
  if World.eq ref_w cur_w then cproof' else begin
    (* Case 2. ref_w is not the reference world of a given CS_BBI proof. *)
    let next_proof =
      match WSeq.pick_wc_exn (fun ws -> worlds_ws ws |! Fn.flip Set.mem ref_w) wseq with
      | WSeq.Mpair (cseq_1, cseq_2), cseq' ->
        if worlds_seq cseq_1 |! Fn.flip Set.mem ref_w then begin
          (* Case 2-1: W_1 in W_1, W_2 contains the reference world *)
          CBuild.construct_exn (CSBBI.Rule.TP (cseq_2.WSeq.world, cseq'.WSeq.world)) (CSBBI.Proof.POne cproof')
        end else begin
          (* Case 2-2: W_2 in W_1, W_2 contains the reference world *)
          CBuild.construct_exn (CSBBI.Rule.Comm (cseq_2.WSeq.world, cseq_1.WSeq.world)) (CSBBI.Proof.POne cproof')
          |! (fun cproof -> CBuild.construct_exn (CSBBI.Rule.TP (cseq_1.WSeq.world, cseq'.WSeq.world)) (CSBBI.Proof.POne cproof))
        end
      | WSeq.Apair (cseq_1, cseq_2), cseq' ->
        if worlds_seq cseq_1 |! Fn.flip Set.mem ref_w then begin
          (* Case 2-3: W_1 in W_1 <W_2> contains the reference world *)
          CBuild.construct_exn (CSBBI.Rule.TC (cseq'.WSeq.world, cseq_1.WSeq.world)) (CSBBI.Proof.POne cproof')
          |! (fun cproof -> 
            CBuild.construct_exn 
              (CSBBI.Rule.Comm (cseq_1.WSeq.world, cseq'.WSeq.world)) (CSBBI.Proof.POne cproof))
          |! (fun cproof -> 
            CBuild.construct_exn 
              (CSBBI.Rule.TP (cseq'.WSeq.world, cseq_2.WSeq.world)) (CSBBI.Proof.POne cproof))
        end else begin
          (* Case 2-4: W_2 in W_1 <W_2> contains the reference world *)
          let cproof'' = 
            CBuild.construct_exn 
              (CSBBI.Rule.TC (cseq'.WSeq.world, cseq_1.WSeq.world)) 
              (CSBBI.Proof.POne cproof') in
          (* match lookup_lm_exn lm cseq'.WSeq.world with *)
          (* | Left -> cproof''  *)
          (* | Right ->  *)
          (*   CBuild.construct_exn  *)
          (*     (CSBBI.Rule.Comm (cseq_1.WSeq.world, cseq'.WSeq.world))  *)
          (*     (CSBBI.Proof.POne cproof'') *)
          cproof''
        end
    in display_exn_aux lm ref_w (display_exn_comm lm next_proof)
  end

let display_exn { LSeq.relations = rc } ref_w cproof =
  try
    let lm = build_lm rc in   
    display_exn_aux lm ref_w cproof
    (* |! display_exn_comm lm *)
  with e -> exn_reraise ~msg:(Error.fails "display") e
    
(** Convert a L_BBI proof into a corresponding CS_BBI proof *)            
let rec convert_p_exn (lrule, lseq, lprem) =
  let _, ({ WSeq.world = ref_w } as cseq), _ as cproof = 
    match lrule with
    | LBBI.Rule.Init (prop, w) -> begin
      try
        CSBBI.Rule.Init prop, convert_s_exn w lseq, CSBBI.Proof.PUnit
      with e -> exn_reraise ~msg:(Error.fails "convert_p_init") e
    end
    | LBBI.Rule.TopR w -> begin
      try
        CSBBI.Rule.TopR, convert_s_exn w lseq, CSBBI.Proof.PUnit
      with e -> exn_reraise ~msg:(Error.fails "convert_p_top_right") e
    end
    | LBBI.Rule.BotL w -> begin
      try
        CSBBI.Rule.BotL, convert_s_exn w lseq, CSBBI.Proof.PUnit
      with e -> exn_reraise ~msg:(Error.fails "convert_p_bot_left") e            
    end
    | LBBI.Rule.NegL (prop, w) -> begin
      try
        let lproof' = LBBI.Proof.match_prem_one lprem 
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof' 
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn (CSBBI.Rule.NegL prop) (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_neg_left") e
    end
    | LBBI.Rule.NegR (prop, w) -> begin
      try
        let lproof' = LBBI.Proof.match_prem_one lprem 
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof' 
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn (CSBBI.Rule.NegR prop) (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_neg_right") e
    end
    | LBBI.Rule.AndL (prop, w) -> begin
      try
        let lproof' = LBBI.Proof.match_prem_one lprem 
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof' 
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn (CSBBI.Rule.AndL prop) (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_and_left") e
    end
    | LBBI.Rule.AndR (prop, w) -> begin
      try
        let lproof_1, lproof_2 = LBBI.Proof.match_prem_two lprem 
                                 |! simpl_unwrap in
        let cproof_1 = convert_p_exn lproof_1
                       |! display_exn (LBBI.Proof.seq_of lproof_1) w in
        let cproof_2 = convert_p_exn lproof_2
                       |! display_exn (LBBI.Proof.seq_of lproof_2) w in
        CBuild.construct_exn (CSBBI.Rule.AndR prop) (CSBBI.Proof.PTwo (cproof_1, cproof_2))
      with e -> exn_reraise ~msg:(Error.fails "convert_p_and_right") e
    end
    | LBBI.Rule.OrL (prop, w) -> begin
      try
        let lproof_1, lproof_2 = LBBI.Proof.match_prem_two lprem 
                                 |! simpl_unwrap in
        let cproof_1 = convert_p_exn lproof_1
                       |! display_exn (LBBI.Proof.seq_of lproof_1) w in
        let cproof_2 = convert_p_exn lproof_2
                       |! display_exn (LBBI.Proof.seq_of lproof_2) w in
        CBuild.construct_exn (CSBBI.Rule.OrL prop) (CSBBI.Proof.PTwo (cproof_1, cproof_2))
      with e -> exn_reraise ~msg:(Error.fails "convert_p_or_left") e
    end
    | LBBI.Rule.OrR (prop, w) -> begin
      try
        let lproof' = LBBI.Proof.match_prem_one lprem 
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof' 
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn (CSBBI.Rule.OrR prop) (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_or_right") e
    end
    | LBBI.Rule.ImplyL (prop, w) -> begin
      try
        let lproof_1, lproof_2 = LBBI.Proof.match_prem_two lprem 
                                 |! simpl_unwrap in
        let cproof_1 = convert_p_exn lproof_1
                       |! display_exn (LBBI.Proof.seq_of lproof_1) w in
        let cproof_2 = convert_p_exn lproof_2
                       |! display_exn (LBBI.Proof.seq_of lproof_2) w in
        CBuild.construct_exn (CSBBI.Rule.ImplyL prop) (CSBBI.Proof.PTwo (cproof_1, cproof_2))
      with e -> exn_reraise ~msg:(Error.fails "convert_p_imply_left") e
    end
    | LBBI.Rule.ImplyR (prop, w) -> begin
      try
        let lproof' = LBBI.Proof.match_prem_one lprem 
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof' 
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn (CSBBI.Rule.ImplyR prop) (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_imply_right") e         
    end
    | LBBI.Rule.UnitL w -> begin
      try
        let lproof' = LBBI.Proof.match_prem_one lprem
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof'
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn CSBBI.Rule.UnitL (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_unit_left") e
    end
    | LBBI.Rule.UnitR w -> begin
      try
        CSBBI.Rule.UnitR, convert_s_exn w lseq, CSBBI.Proof.PUnit
      with e -> exn_reraise ~msg:(Error.fails "convert_p_unit_right") e
    end
    | LBBI.Rule.StarL ((prop, w), (world_A, world_B)) -> begin
      try
        let lproof' = LBBI.Proof.match_prem_one lprem
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof'
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn (CSBBI.Rule.StarL (prop, (world_A, world_B))) (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_star_left") e
    end
    | LBBI.Rule.StarR ({ LSeq.parent = w; LSeq.lchild = w_A; LSeq.rchild = w_B; }, prop) -> begin
      try
        let lproof_1, lproof_2 = LBBI.Proof.match_prem_two lprem 
                                 |! simpl_unwrap in
        let cproof_1 = convert_p_exn lproof_1
                       |! display_exn (LBBI.Proof.seq_of lproof_1) w in
        let cproof_2 = convert_p_exn lproof_2
                       |! display_exn (LBBI.Proof.seq_of lproof_2) w in
        CBuild.construct_exn (CSBBI.Rule.StarR ((w_A, w_B), prop)) (CSBBI.Proof.PTwo (cproof_1, cproof_2))
      with e -> exn_reraise ~msg:(Error.fails "convert_p_star_right") e
    end
    | LBBI.Rule.WandL ({ LSeq.parent = w_B; LSeq.lchild = w; LSeq.rchild = w_A; }, prop) -> begin
      try
        let lproof_1, lproof_2 = LBBI.Proof.match_prem_two lprem 
                                 |! simpl_unwrap in
        let cproof_1 = convert_p_exn lproof_1
                       |! display_exn (LBBI.Proof.seq_of lproof_1) w in
        let cproof_2 = convert_p_exn lproof_2
                       |! display_exn (LBBI.Proof.seq_of lproof_2) w in
        CBuild.construct_exn (CSBBI.Rule.WandL ((w_A, w_B), prop)) (CSBBI.Proof.PTwo (cproof_1, cproof_2))
      with e -> exn_reraise ~msg:(Error.fails "convert_p_wand_left") e
    end
    | LBBI.Rule.WandR ((prop, w), (world_A, world_B)) -> begin
      try
        let lproof' = LBBI.Proof.match_prem_one lprem
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof'
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn (CSBBI.Rule.WandR (prop, (world_A, world_B))) (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_wand_right") e
    end      
    | LBBI.Rule.Comm { LSeq.parent = w; LSeq.lchild = w_l; LSeq.rchild = w_r; } -> begin
      try
        let lproof' = LBBI.Proof.match_prem_one lprem
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof'
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn (CSBBI.Rule.Comm (w_l, w_r)) (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_comm") e
    end
    | LBBI.Rule.Assoc ((rel_1, rel_2), (w_n, rn_1, rn_2, rn_3)) -> begin
      try
        let { LSeq.parent = w; LSeq.lchild = w'; LSeq.rchild = w_3; } = rel_1 in
        let { LSeq.lchild = w_1; LSeq.rchild = w_2; } = rel_2 in
        let lproof' = LBBI.Proof.match_prem_one lprem
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof'
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn (CSBBI.Rule.Assoc (((w', w_3), (w_1, w_2)), (w_n, rn_1, rn_2, rn_3))) (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_assoc") e
    end
    | LBBI.Rule.ZeroU (w, (w_e, rn)) -> begin
      try
        let lproof' = LBBI.Proof.match_prem_one lprem
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof'
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn (CSBBI.Rule.ZeroU ((), (rn, w_e))) (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_zero_up") e
    end
    | LBBI.Rule.ZeroD ({ LSeq.parent = w; LSeq.lchild = w_c1; LSeq.rchild = w_c2 }, rn) -> begin
      try
        let lproof' = LBBI.Proof.match_prem_one lprem
                      |! simpl_unwrap in
        let cproof' = convert_p_exn lproof'
                      |! display_exn (LBBI.Proof.seq_of lproof') w in
        CBuild.construct_exn (CSBBI.Rule.ZeroD ((w_c1, w_c2), rn)) (CSBBI.Proof.POne cproof')
      with e -> exn_reraise ~msg:(Error.fails "convert_p_zero_down") e
    end
  in 
  let () = begin
    let expected_cseq = convert_s_exn ref_w lseq in
    try
      WSeq.eq expected_cseq cseq |! simpl_unwrap
    with e ->
      let msg = String.concat ["invariant is violated for the rule:\n"; 
                               LBBI.Rule.sexp_of_t lrule |! Sexp.to_string_hum; "\n\n";
                               "Expected :\n";
                               WSeq.sexp_of_t expected_cseq |! Sexp.to_string_hum; "\n\n";
                               "Given :\n";
                               WSeq.sexp_of_t cseq |! Sexp.to_string_hum; "\n\n";
                               "LSeq :\n";
                               LSeq.sexp_of_t lseq |! Sexp.to_string_hum; "\n\n"]
      in exn_reraise ~msg:msg e
  end in cproof 

let convert lproof =
  try
    convert_p_exn lproof |! wrap
  with e -> exn_wrap_err ~msg:(Error.fails "ConvertLC.convert") e

let convert_exn lproof = 
  try
    convert lproof |! simpl_unwrap
  with 
  | Failure msg -> 
    let () = print_string msg |! print_newline in
    exn_failure "ConvertLC.convert"    

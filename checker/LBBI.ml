(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

module Rule =
struct
  let id = "LBBI"

  type seq = LSeq.t
  with sexp

  type premise =
  | PUnit
  | POne of seq
  | PTwo of seq * seq
  with sexp

  let match_prem_unit = function
    | PUnit -> wrap ()
    | _ -> wrap_err "Rule.PUnit is expected, but isn't given."

  let match_prem_one = function
    | POne lseq -> wrap lseq
    | _ -> wrap_err "Rule.POne is expected, but isn't given."
      
  let match_prem_two = function
    | PTwo (lseq_l, lseq_r) -> wrap (lseq_l, lseq_r)
    | _ -> wrap_err "Rule.PTwo is expected, but isn't given."

  let match_prem_unit_exn prem = match_prem_unit prem |! simpl_unwrap
  let match_prem_one_exn prem = match_prem_one prem |! simpl_unwrap
  let match_prem_two_exn prem = match_prem_two prem |! simpl_unwrap

  type t =
  | Init of (Prop.t * World.t) 
  | TopR of World.t 
  | BotL of World.t 
  | NegL of (Prop.t * World.t) 
  | NegR of (Prop.t * World.t) 
  | AndL of (Prop.t * World.t) 
  | AndR of (Prop.t * World.t) 
  | OrL of (Prop.t * World.t) 
  | OrR of (Prop.t * World.t) 
  | ImplyL of (Prop.t * World.t) 
  | ImplyR of (Prop.t * World.t) 
  | UnitL of World.t 
  | UnitR of World.t 
  | StarL of (Prop.t * World.t) * (World.t * World.t)
  | StarR of (LSeq.world_rel * Prop.t) 
  | WandL of (LSeq.world_rel * Prop.t) 
  | WandR of (Prop.t * World.t) * (World.t * World.t)
  | Comm of LSeq.world_rel
  | Assoc of (LSeq.world_rel * LSeq.world_rel) * (World.t * World.rename * World.rename * World.rename)
  | ZeroU of World.t * (World.t * World.rename)
  | ZeroD of LSeq.world_rel * World.rename
  with sexp


  (***************************************************************)
  (* val valid_seq: t -> bool *)
  (* worlds are acyclic and connected. *)
  (***************************************************************)
  module G = Graph.Imperative.Graph.Abstract(World)
  module Com = Graph.Components.Make(G)
  module Dfs = Graph.Traverse.Dfs(G)

  let valid_seq ({LSeq.worlds=ws; LSeq.relations=rel; LSeq.tcontext=tc; LSeq.fcontext=fc;} as seq) = 
    try
      LSeq.syntactic_well_formed seq |! simpl_unwrap;
    (* relations are acyclic *)
      let graph = G.create ~size:(List.length ws) () in
      let vertices = List.map ws ~f:(fun w -> w, G.V.create w) in
      let () = List.iter vertices ~f:(fun (_,v) -> G.add_vertex graph v) in
      let () = List.iter rel
        ~f:(fun rel ->
          let vertex_of w =
            List.Assoc.find_exn vertices ~equal:World.eq w in
          G.add_edge graph (vertex_of rel.LSeq.parent) (vertex_of rel.LSeq.lchild);
          G.add_edge graph (vertex_of rel.LSeq.parent) (vertex_of rel.LSeq.rchild)) in
    (* an undireced graph is connected iff it has only one strongly connected component *)
      if fst (Com.scc graph) <> 1 then
        wrap_err "World structure is not connected." |! simpl_unwrap
      else if Dfs.has_cycle graph then
        wrap_err "World structure is not acyclic." |! simpl_unwrap
      else
        wrap ()
    with
    | e -> exn_wrap_err ~msg:("valid_seq failed with:") e


  (* val project_seq :  *)
  (*    ws_proj:(World.t -> bool) -> *)
  (*    rel_proj:(world_rel -> bool) -> *)
  (*    tcontext_proj:(wstate * World.t -> bool) -> *)
  (*    fcontext_proj:(Prop.t * World.t -> bool) -> *)
  (*    seq -> seq *)

  let project_seq ~ws_proj:ws_proj ~rel_proj:rel_proj ~tc_proj:tc_proj ~fc_proj:fc_proj 
      { LSeq.worlds = ws; LSeq.relations = rs; LSeq.tcontext=tc; LSeq.fcontext=fc; } =
    { LSeq.worlds = List.rev_filter ~f:ws_proj ws;
      LSeq.relations = List.rev_filter ~f:rel_proj rs;
      LSeq.tcontext = List.rev_filter ~f:tc_proj tc;
      LSeq.fcontext = List.rev_filter ~f:fc_proj fc;
    }

  let forward rule premise = 
    try begin
      match  rule, premise with
      | Init _, _ 
      | TopR _, _ 
      | BotL _, _ 
      | UnitR _, _ -> wrap_err ("Cannot forward the rule: " ^ (sexp_of_t rule |! Sexp.to_string_hum)) |! simpl_unwrap

      | NegL (Prop.Neg prop as neg_prop, w), POne (seq) -> 
        seq
        |! LSeq.remove_fc (prop, w)
          >> LSeq.add_tc_prop (neg_prop, w)
          >> wrap

      | NegR (Prop.Neg prop as neg_prop, w), POne (seq) -> 
        seq
        |! LSeq.remove_tc_prop (prop, w)
          >> LSeq.add_fc (neg_prop, w)
          >> wrap

      | AndL (Prop.And (prop_a, prop_b) as and_prop, w), POne (seq) -> 
        seq
        |! LSeq.remove_tc_prop (prop_a, w)
          >> LSeq.remove_tc_prop (prop_b, w)
          >> LSeq.add_tc_prop (and_prop, w)
          >> wrap

      | AndR (Prop.And (prop_a, prop_b) as and_prop, w), PTwo (seq1, seq2) ->
        seq2
        |! LSeq.remove_fc (prop_b, w)
        |! unwrap "Deleting PropB failed"
        |! ignore;
        (seq1
        |! LSeq.remove_fc (prop_a, w)
          >> LSeq.add_fc (and_prop, w)
          >> wrap)

      | OrL (Prop.Or (prop_a, prop_b) as or_prop, w), PTwo (seq1, seq2) -> 
        (* seq2 *)
        (* |! LSeq.remove_tc_prop (prop_b, w) *)
        (*   >> unwrap "Deleting PropB failed" *)
        (* |! ignore; *)
        seq1
        |! LSeq.remove_tc_prop (prop_a, w)
          >> LSeq.add_tc_prop (or_prop, w)
          >> wrap        

      | OrR (Prop.Or (prop_a, prop_b) as or_prop, w), POne (seq) -> 
        seq 
        |! LSeq.remove_fc (prop_a, w)
          >> LSeq.remove_fc (prop_b, w)
          >> LSeq.add_fc (or_prop, w)
          >> wrap

      | ImplyL (Prop.Imply (prop_a, prop_b) as imply_prop, w), PTwo (seq1, seq2) -> 
        seq2
        |! LSeq.remove_tc_prop (prop_b, w)
        |! unwrap "Deleting PropB failed"
        |! ignore;
        seq1
        |! LSeq.remove_fc (prop_a, w)
          >> LSeq.add_tc_prop (imply_prop, w)
          >> wrap

      | ImplyR (Prop.Imply (prop_a, prop_b) as imply_prop, w), POne (seq) -> 
        seq 
        |! LSeq.remove_tc_prop (prop_a, w)
          >> LSeq.remove_fc (prop_b, w)
          >> LSeq.add_fc (imply_prop, w)
          >> wrap

      | UnitL w, POne (seq) -> 
        seq 
        |! LSeq.remove_tc_mzero w
          >> LSeq.add_tc_prop (Prop.Unit, w)
          >> wrap

      | StarL ((Prop.Star (prop_a, prop_b) as star_prop, w), (w1, w2)), POne (seq) ->
        seq 
        |! LSeq.remove_wc w1
          >> LSeq.remove_wc w2
          >> LSeq.remove_rc {LSeq.parent=w; LSeq.lchild=w1; LSeq.rchild=w2}
          >> LSeq.remove_tc_prop (prop_a, w1)
          >> LSeq.remove_tc_prop (prop_b, w2)
          >> LSeq.add_tc_prop (star_prop, w)
          >> wrap

      | StarR ({LSeq.parent=w; LSeq.lchild=w1; LSeq.rchild=w2} as rel, (Prop.Star (prop_a, prop_b) as star_prop)), PTwo (seq1, seq2) ->
        LSeq.exists_rc rel seq1 |! unwrap "world_rel check Premise1";
        LSeq.exists_fc (star_prop, w) seq1 |! unwrap "Star prop check for Premise1";
        LSeq.exists_rc rel seq2 |! unwrap "world_rel check Premise2";
        LSeq.exists_fc (star_prop, w) seq2 |! unwrap "Star prop check for Premise2";
        LSeq.exists_fc (prop_b, w2) seq2 |! unwrap "PropB check for Premise2";
        seq1
        |! LSeq.remove_fc (prop_a, w1)
          >> wrap
            
      | WandL ({LSeq.parent=w2; LSeq.lchild=w; LSeq.rchild=w1} as rel, (Prop.Wand (prop_a, prop_b) as wand_prop)), PTwo (seq1, seq2) ->
        LSeq.exists_rc rel seq1 |! unwrap " world_rel check Premise2";
        LSeq.exists_tc_prop (wand_prop, w) seq1 |! unwrap "Wand prop check for Premise1";
        LSeq.exists_rc rel seq2 |! unwrap " world_rel check Premise2";
        LSeq.exists_tc_prop (wand_prop, w) seq2 |! unwrap "Wand prop check for Premise2";
        LSeq.exists_tc_prop (prop_b, w2) seq2 |! unwrap "PropB check for Premise2";
        seq1 
        |! LSeq.remove_fc (prop_a, w1)
          >> wrap

      | WandR ((Prop.Wand (prop_a, prop_b) as wand_prop, w), (w1, w2)), POne (seq) ->
        seq 
        |! LSeq.remove_wc w1
          >> LSeq.remove_wc w2
          >> LSeq.remove_rc {LSeq.parent=w2; lchild=w; rchild=w1;}
          >> LSeq.remove_tc_prop (prop_a, w1)
          >> LSeq.remove_fc (prop_b, w2)
          >> LSeq.add_fc (wand_prop, w)
          >> wrap

      | Comm ({LSeq.parent=w; LSeq.lchild=w1; LSeq.rchild=w2} as rel), POne (seq) ->
        seq
        |! LSeq.remove_rc {LSeq.parent=w; LSeq.lchild=w2; LSeq.rchild=w1} 
          >> LSeq.add_rc rel
          >> wrap
            
      (* Do not check many things... *)
      | Assoc ((({LSeq.parent=w; LSeq.lchild=w'; LSeq.rchild=w3} (* as rel1 *)),
                ({LSeq.parent=w'_dup; LSeq.lchild=w1; LSeq.rchild=w2} (* as rel2 *))),
               (w'', rename1, rename2, rename3)), POne (seq) when World.eq w' w'_dup ->
        (* LSeq.exists_rc rel1 seq |! simpl_unwrap; *)
        (* LSeq.exists_rc rel2 seq |! simpl_unwrap; *)
        (* t these test should be done on the result *)
        (* let w1_new = World.rename rename1 w1 |! simpl_unwrap in *)
        (* let w2_new = World.rename rename2 w2 |! simpl_unwrap in *)
        (* let w3_new = World.rename rename3 w3 |! simpl_unwrap in *)
        if Map.has_key rename1 w'' then
          wrap_err "w'' was not fresh" |! simpl_unwrap
        else
          seq
        (* |! LSeq.remove_wc w'' *)
        (* >> LSeq.remove_rc {LSeq.parent=w; LSeq.lchild=w1_new; LSeq.rchild=w''} *)
        (* >> LSeq.remove_rc {LSeq.parent=w''; LSeq.lchild=w2_new; LSeq.rchild=w3_new} *)
        (* |! simpl_unwrap *)
          |! project_seq
              ~ws_proj:(Map.has_key rename1)
              ~rel_proj:(fun rel ->
                Map.has_key rename1 rel.LSeq.parent
                && Map.has_key rename1 rel.LSeq.lchild 
                && Map.has_key rename1 rel.LSeq.rchild)
              ~tc_proj:(fun (_, w) -> Map.has_key rename1 w)
              ~fc_proj:(fun (_, w) -> Map.has_key rename1 w)
          |! wrap

      (* Do not check all conditions *)
      | ZeroU (w, (w'', rename)), POne (seq) ->
        (* LSeq.exists_wc w seq |! simpl_unwrap; *)
        (* let w_new = World.rename rename w |! simpl_unwrap in *)
        seq
        (* |! LSeq.remove_wc w'' *)
        (*   >> LSeq.remove_rc {LSeq.parent=w; LSeq.lchild=w_new; LSeq.rchild=w''} *)
        (*   >> LSeq.remove_tc_mzero w'' *)
        (* |! simpl_unwrap *)
        |! project_seq
            ~ws_proj:(Map.has_key rename)
            ~rel_proj:(fun rel ->
              Map.has_key rename rel.LSeq.parent
              && Map.has_key rename rel.LSeq.lchild 
              && Map.has_key rename rel.LSeq.rchild)
            ~tc_proj:(fun (_, w) -> Map.has_key rename w)
            ~fc_proj:(fun (_, w) -> Map.has_key rename w)
        |! wrap

      | ZeroD ({LSeq.parent=w; LSeq.lchild=w1; LSeq.rchild=w2} (* as rel *), rename), POne (seq) ->
        (* LSeq.exists_rc rel seq |! simpl_unwrap; *)
        (* LSeq.exists_tc_mzero w2 seq |! simpl_unwrap; *)
        let new_worlds = Map.data rename in
        let w_new = World.rename rename w1 |! simpl_unwrap in
        (* TODO: w_new = w *)
        let safe_new_worlds = List.filter ~f:((<>) w_new) new_worlds in
        let interm_seq = 
          seq
          |! project_seq
              ~ws_proj:(Map.has_key rename)
              ~rel_proj:(fun rel ->
                not ((List.mem rel.LSeq.parent safe_new_worlds) 
                     || (List.mem rel.LSeq.lchild safe_new_worlds) 
                     || (List.mem rel.LSeq.rchild safe_new_worlds)))
              ~tc_proj:(fun (_, w) -> List.mem w safe_new_worlds |! not)
              ~fc_proj:(fun (_, w) -> List.mem w safe_new_worlds |! not) in
        { interm_seq with
          LSeq.tcontext = List.rev_map ~f:(function (a,b) when World.eq w_new b -> (a,w) | c -> c) interm_seq.LSeq.tcontext;
          LSeq.fcontext = List.rev_map ~f:(function (a,b) when World.eq w_new b -> (a,w) | c -> c) interm_seq.LSeq.fcontext;
        }
        |! wrap

      | _ -> wrap_err ("Invalid rule * premise combination to forward:"
                       ^ "\nPremise:\n"
                       ^ (sexp_of_premise premise |! Sexp.to_string_hum)
                       ^ "\nRule:\n"
                       ^ (sexp_of_t rule |! Sexp.to_string_hum)) |! simpl_unwrap
    end 
    with
    | e -> exn_wrap_err ~msg:("Foward failed with " ^ (sexp_of_t rule |! Sexp.to_string_hum)) e

  let wrap_p_one seq = wrap (POne seq)
  let wrap_p_two (seq1, seq2) = wrap (PTwo (seq1, seq2))

  let backward rule seq = 
    try begin
      match rule with
      | Init (prop_w) -> 
        LSeq.exists_tc_prop prop_w seq |! simpl_unwrap;
        LSeq.exists_fc prop_w seq |! simpl_unwrap;
        wrap PUnit
          
      | TopR (w) -> 
        LSeq.exists_fc (Prop.Top, w) seq |! simpl_unwrap;
        wrap PUnit

      | BotL w -> 
        LSeq.exists_tc_prop (Prop.Bot, w) seq |! simpl_unwrap;
        wrap PUnit

      | NegL (Prop.Neg prop as neg_prop, w) -> 
        seq
        |! LSeq.remove_tc_prop (neg_prop, w)
          >> LSeq.add_fc (prop, w)
          >> wrap_p_one

      | NegR (Prop.Neg prop as neg_prop, w) -> 
        seq
        |! LSeq.remove_fc (neg_prop, w)
          >> LSeq.add_tc_prop (prop, w)
          >> wrap_p_one

      | AndL (Prop.And (prop_a, prop_b) as and_prop, w) -> 
        seq
        |! LSeq.remove_tc_prop (and_prop, w)
          >> LSeq.add_tc_prop (prop_a, w)
          >> LSeq.add_tc_prop (prop_b, w)
          >> wrap_p_one

      | AndR (Prop.And (prop_a, prop_b) as and_prop, w) -> 
        let base_seq = seq |! LSeq.remove_fc (and_prop, w) |! simpl_unwrap in
        (base_seq
         |! LSeq.add_fc (prop_a, w)
         |! unwrap "Add prop_A failed", (* unlikely failed *)
         base_seq
         |! LSeq.add_fc (prop_b, w)
         |! unwrap "Add prop_B failed") (* unlikely failed *)
        |! wrap_p_two

      | OrL (Prop.Or (prop_a, prop_b) as or_prop, w) -> 
        let base_seq = seq |! LSeq.remove_tc_prop (or_prop, w) |! simpl_unwrap in
        (base_seq
         |! LSeq.add_tc_prop (prop_a, w)
         |! unwrap "Add prop_A failed",
         base_seq
         |! LSeq.add_tc_prop (prop_b, w)
         |! unwrap "Add prop_B failed")
        |! wrap_p_two

      | OrR (Prop.Or (prop_a, prop_b) as or_prop, w) -> 
        seq 
        |! LSeq.remove_fc (or_prop, w)
          >> LSeq.add_fc (prop_a, w)
          >> LSeq.add_fc (prop_b, w)
          >> wrap_p_one

      | ImplyL (Prop.Imply (prop_a, prop_b) as imply_prop, w) -> 
        let base_seq_result = seq |! LSeq.remove_tc_prop (imply_prop, w) in
        (base_seq_result
         >> LSeq.add_fc (prop_a, w),
         base_seq_result
         >> LSeq.add_tc_prop (prop_b, w))
        |! merge_result_pair
          >> wrap_p_two

      | ImplyR (Prop.Imply (prop_a, prop_b) as imply_prop, w) -> 
        seq 
        |! LSeq.remove_fc (imply_prop, w)
          >> LSeq.add_tc_prop (prop_a, w)
          >> LSeq.add_fc (prop_b, w)
          >> wrap_p_one

      | UnitL w -> 
        seq 
        |! LSeq.remove_tc_prop (Prop.Unit, w)
          >> LSeq.add_tc_mzero w
          >> wrap_p_one

      | UnitR w -> 
        LSeq.exists_tc_mzero w seq |! simpl_unwrap;
        LSeq.exists_fc (Prop.Unit, w) seq |! simpl_unwrap;
        wrap PUnit

      | StarL ((Prop.Star (prop_a, prop_b) as star_prop, w), (w1, w2)) ->
        seq 
        |! LSeq.remove_tc_prop (star_prop, w)
          >> LSeq.add_wc w1  (* freshness of w1 is checked here *)
          >> LSeq.add_wc w2  (* freshness of w2 is checked here *)
          >> LSeq.add_rc {LSeq.parent=w; LSeq.lchild=w1; LSeq.rchild=w2}
          >> LSeq.add_tc_prop (prop_a, w1)
          >> LSeq.add_tc_prop (prop_b, w2)
          >> wrap_p_one

      | StarR ({LSeq.parent=w; LSeq.lchild=w1; LSeq.rchild=w2} as rel, (Prop.Star (prop_a, prop_b) as star_prop)) ->
        LSeq.exists_rc rel seq |! simpl_unwrap;
        LSeq.exists_fc (star_prop, w) seq |! simpl_unwrap;
        (seq 
         |! LSeq.add_fc (prop_a, w1),
         seq
         |! LSeq.add_fc (prop_b, w2))
        |! merge_result_pair
          >> wrap_p_two
            
      | WandL ({LSeq.parent=w2; LSeq.lchild=w; LSeq.rchild=w1} as rel, (Prop.Wand (prop_a, prop_b) as wand_prop)) ->
        LSeq.exists_rc rel seq |! simpl_unwrap;
        LSeq.exists_tc_prop (wand_prop, w) seq |! simpl_unwrap;
        (seq 
         |! LSeq.add_fc (prop_a, w1),
         seq
         |! LSeq.add_tc_prop (prop_b, w2))
        |! merge_result_pair
          >> wrap_p_two

      | WandR ((Prop.Wand (prop_a, prop_b) as wand_prop, w), (w1, w2)) ->
        seq 
        |! LSeq.remove_fc (wand_prop, w)
          >> LSeq.add_wc w1  (* freshness of w1 is checked here *)
          >> LSeq.add_wc w2  (* freshness of w2 is checked here *)
          >> LSeq.add_rc {LSeq.parent=w2; lchild=w; rchild=w1;}
          >> LSeq.add_tc_prop (prop_a, w1)
          >> LSeq.add_fc (prop_b, w2)
          >> wrap_p_one

      | Comm ({LSeq.parent=w; LSeq.lchild=w1; LSeq.rchild=w2} as rel) ->
        seq
        |! LSeq.remove_rc rel
          >> LSeq.add_rc {LSeq.parent=w; LSeq.lchild=w2; LSeq.rchild=w1}
          >> wrap_p_one

      | Assoc ((({LSeq.parent=w; LSeq.lchild=w'; LSeq.rchild=w3} as rel1),
                ({LSeq.parent=w'_dup; LSeq.lchild=w1; LSeq.rchild=w2} as rel2)),
               (w'', rename1, rename2, rename3)) when World.eq w' w'_dup ->
        (* Renamings are valid? *)
        seq.LSeq.worlds
        |! eq_list (Map.keys rename1)
        |! unwrap "rename1's domain <> worlds";
        seq.LSeq.worlds
        |! eq_list (Map.keys rename2)
        |! unwrap "rename2's domain <> worlds";
        seq.LSeq.worlds
        |! eq_list (Map.keys rename3)
        |! unwrap "rename3's domain <> worlds";
        seq.LSeq.worlds 
        |! List.rev_append (Map.data rename1) 
        |! List.rev_append (Map.data rename2)
        |! List.rev_append (Map.data rename3)
        |! List.exn_if_dup ~compare:World.compare ~context:"Renamings' results are not distinct." ~to_sexp:World.sexp_of_t;
        (* Convert! *)
        LSeq.exists_rc rel1 seq |! simpl_unwrap;
        LSeq.exists_rc rel2 seq |! simpl_unwrap;
        let seq1 = LSeq.apply_rename rename1 seq |! simpl_unwrap in
        let seq2 = LSeq.apply_rename rename2 seq |! simpl_unwrap in
        let seq3 = LSeq.apply_rename rename3 seq |! simpl_unwrap in
        let w1_new = World.rename rename1 w1 |! simpl_unwrap in
        let w2_new = World.rename rename2 w2 |! simpl_unwrap in
        let w3_new = World.rename rename3 w3 |! simpl_unwrap in
        seq
        |! LSeq.merge seq1
          >> LSeq.merge seq2
          >> LSeq.merge seq3
          >> LSeq.add_wc w''  (* freshness of w'' is checked here *)
          >> LSeq.add_rc {LSeq.parent=w; LSeq.lchild=w1_new; LSeq.rchild=w''}
          >> LSeq.add_rc {LSeq.parent=w''; LSeq.lchild=w2_new; LSeq.rchild=w3_new}
          >> wrap_p_one

      | ZeroU (w, (w'', rename)) ->
        (* Renamings are valid? *)
        seq.LSeq.worlds
        |! eq_list (Map.keys rename)
        |! unwrap "rename's domain <> worlds";
        seq.LSeq.worlds 
        |! List.rev_append (Map.data rename)
        |! List.exn_if_dup ~compare:World.compare ~context:"Renaming's results are not distinct."  ~to_sexp:World.sexp_of_t;
        (* Convert! *)
        LSeq.exists_wc w seq |! simpl_unwrap;
        let seq1 = LSeq.apply_rename rename seq |! simpl_unwrap in
        let w_new = World.rename rename w |! simpl_unwrap in
        seq
        |! LSeq.merge seq1
          >> LSeq.add_wc w''  (* freshness of w'' is checked here *)
          >> LSeq.add_rc {LSeq.parent=w; LSeq.lchild=w_new; LSeq.rchild=w''}
          >> LSeq.add_tc_mzero w''
          >> wrap_p_one

      | ZeroD ({LSeq.parent=w; LSeq.lchild=w1; LSeq.rchild=w2} as rel, rename) ->
        (* Renamings are valid? *)
        seq.LSeq.worlds
        |! eq_list (Map.keys rename)
        |! unwrap "rename's domain <> worlds";
        let w1_new = World.rename rename w1 |! simpl_unwrap in
        if World.eq w1_new w |! not then begin
          wrap_err ("renaming is wrong: "
                    ^ World.to_string w1 
                    ^ " is expected to be mapped to "
                    ^ World.to_string w
                    ^ "; but "
                    ^ World.to_string w1_new)
          |! simpl_unwrap
        end;
        seq.LSeq.worlds 
        |! List.filter ~f:(fun x -> World.eq w x |! not)
        |! List.rev_append (Map.data rename)
        |! List.exn_if_dup ~compare:World.compare ~context:"Renaming's results are not distinct."  ~to_sexp:World.sexp_of_t;
        (* Convert! *)
        LSeq.exists_rc rel seq |! simpl_unwrap;
        LSeq.exists_tc_mzero w2 seq |! simpl_unwrap;
        let seq1 = LSeq.apply_rename rename seq |! simpl_unwrap in
        seq
        |! LSeq.remove_wc w (* w is also in seq1. *)
          >> LSeq.merge seq1
          >> wrap_p_one

      (*  *)
      | _ -> wrap_err "Invalid rule combination." |! simpl_unwrap
    end
    with
    | List.Duplicate_found (dup, msg) ->
      wrap_err ("Backward failed with " ^ (sexp_of_t rule |! Sexp.to_string_hum)
                ^ "\n" ^ msg 
                ^ "\nDuplicated found: "
                ^ (dup () |! Sexp.to_string_hum))
    | e -> exn_wrap_err ~msg:("Backward failed with " ^ (sexp_of_t rule |! Sexp.to_string_hum)) e


  let rule_to_tex_command = function
    | Init _ -> "\\RLBinit"
    | TopR _ -> "\\RLBtopright"
    | BotL _ -> "\\RLBbotright"
    | NegL _ -> "\\RLBnegleft"
    | NegR _ -> "\\RLBnegright"
    | AndL _ -> "\\RLBandleft"
    | AndR _ -> "\\RLBandright"
    | OrL _ -> "\\RLBorleft"
    | OrR _ -> "\\RLBorright"
    | ImplyL _ -> "\\RLBimplyleft"
    | ImplyR _ -> "\\RLBimplyright"
    | UnitL _ -> "\\RLBunitleft"
    | UnitR _ -> "\\RLBunitright"
    | StarL _ -> "\\RLBstarleft"
    | StarR _ -> "\\RLBstarright"
    | WandL _ -> "\\RLBwandleft"
    | WandR _ -> "\\RLBwandright"
    | Comm _ -> "\\RLBcomm"
    | Assoc _ -> "\\RLBassoc"
    | ZeroU _ -> "\\RLBmultzeroup"
    | ZeroD _ -> "\\RLBmultzerodown"


  let no_highlight = fun _ -> false
  let rel_eq rel1 rel2 = 
    World.eq rel1.LSeq.parent rel2.LSeq.parent
    && World.eq rel1.LSeq.lchild rel2.LSeq.lchild
    && World.eq rel1.LSeq.rchild rel2.LSeq.rchild
  let tc_eq_prop (prop1, w1) (wstate2, w2) = (LSeq.Prop prop1 = wstate2) && (World.eq w1 w2)
  let tc_eq_mzero w1 (wstate2, w2) = (LSeq.Mzero = wstate2) && (World.eq w1 w2)
  let fc_eq (prop1, w1) (prop2, w2) = prop1 = prop2 && World.eq w1 w2

  let seq_to_tex = function
    | Init prop_w -> 
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop_w) 
        ~fc_highlight:(fc_eq prop_w) 
    | TopR w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq (Prop.Top, w))
    | BotL w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop (Prop.Bot, w))
        ~fc_highlight:no_highlight
    | NegL prop_w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop_w)
        ~fc_highlight:no_highlight
    | NegR prop_w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop_w)
    | AndL prop_w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop_w)
        ~fc_highlight:no_highlight
    | AndR prop_w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop_w)
    | OrL prop_w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop_w)
        ~fc_highlight:no_highlight
    | OrR prop_w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop_w)
    | ImplyL prop_w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop_w)
        ~fc_highlight:no_highlight
    | ImplyR prop_w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop_w)
    | UnitL w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop (Prop.Unit, w))
        ~fc_highlight:no_highlight
    | UnitR w ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:(tc_eq_mzero w)
        ~fc_highlight:(fc_eq (Prop.Unit, w))
    | StarL (prop_w, _) ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop_w)
        ~fc_highlight:no_highlight
    | StarR (rel, prop) ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:(rel_eq rel)
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq (prop, rel.LSeq.parent))
    | WandL (rel, prop) ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:(rel_eq rel)
        ~tc_highlight:(tc_eq_prop (prop, rel.LSeq.parent))
        ~fc_highlight:no_highlight
    | WandR (prop_w, _) ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop_w)
    | Comm rel ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:(rel_eq rel)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | Assoc ((rel1, rel2), _) ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:(fun rel -> rel_eq rel1 rel || rel_eq rel2 rel)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | ZeroU (w, _) ->
      LSeq.to_tex 
        ~w_highlight:(World.eq w)
        ~rel_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | ZeroD (rel, _) ->
      LSeq.to_tex 
        ~w_highlight:no_highlight
        ~rel_highlight:(rel_eq rel)
        ~tc_highlight:(tc_eq_mzero rel.LSeq.rchild)
        ~fc_highlight:no_highlight

  let seq_eq = LSeq.eq
end

module Proof = ProofFn (Rule)

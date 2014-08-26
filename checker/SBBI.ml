(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

module Rule =
struct
  let id = "SBBI"

  type seq = WSeq.t with sexp

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

  type split = {
    selected_tc: WSeq.state list;
    selected_fc: Prop.t list;
    selected_wc: (World.t * World.t) list;
  }
  with sexp

  type t =
  | Init
  | TopL
  | TopR
  | BotL
  | BotR
  | NegL of Prop.t 
  | NegR of Prop.t 
  | AndL of Prop.t 
  | AndR of Prop.t * split
  | OrL of Prop.t * split
  | OrR of Prop.t 
  | ImplyL of Prop.t * split
  | ImplyR of Prop.t 
  | UnitL
  | UnitR
  | StarL of Prop.t * (World.t * World.t)
  | StarR
  | WandL
  | WandR of Prop.t * (World.t * World.t)
  | TC of (World.t * World.t)
  | TP of (World.t * World.t)
  | WeakL of WSeq.state
  | WeakR of Prop.t
  | WeakW of (World.t * World.t)        (* Weakening for Mpair/Apair *)
  | ContraL of WSeq.state
  | ContraR of Prop.t 
  | ContraW of (World.t * World.t * World.rename)
  | Comm of (World.t * World.t)
  | Assoc of (World.t * World.t) * World.t 
  | ZeroU of split * (World.t * World.t)
  | ZeroD of (World.t * World.t) 
  with sexp

  let valid_seq = WSeq.syntactic_well_formed

  (* let mpair_with_worlds w_A w_B = function *)
  (*   | WSeq.Mpair (wseq_A, wseq_B) ->  *)
  (*     World.eq w_A wseq_A.WSeq.world && World.eq w_B wseq_B.WSeq.world *)
  (*   | _ -> false *)

  (* let apair_with_worlds w_A w_B = function *)
  (*   | WSeq.Apair (wseq_A, wseq_B) ->  *)
  (*     World.eq w_A wseq_A.WSeq.world && World.eq w_B wseq_B.WSeq.world *)
  (*   | _ -> false *)

  (* let apair_with_sibling w_s = function *)
  (*   | WSeq.Apair (wseq_s, _) ->  *)
  (*     World.eq w_s wseq_s.WSeq.world  *)
  (*   | _ -> false *)

  (* let mpair_with_rchild w_r = function *)
  (*   | WSeq.Mpair (_, wseq_r) ->  *)
  (*     World.eq w_r wseq_r.WSeq.world *)
  (*   | _ -> false *)

  (* let ws_with_worlds w_1 w_2 = function *)
  (*   | WSeq.Mpair (wseq_1, wseq_2) | WSeq.Apair (wseq_1, wseq_2) ->  *)
  (*     World.eq w_1 wseq_1.WSeq.world && World.eq w_2 wseq_2.WSeq.world *)
    
  (* let ext_ws_mpair = function *)
  (*   | WSeq.Mpair (wseq_A, wseq_B) -> wrap (wseq_A, wseq_B) *)
  (*   | _ ->  *)
  (*     String.concat ["A world state of the form W, W is expected, "; *)
  (*                    "but a given world state is of the form W<W>."] *)
  (*     |! wrap_err *)

  (* let ext_ws_apair = function *)
  (*   | WSeq.Apair (wseq_A, wseq_B) -> wrap (wseq_A, wseq_B) *)
  (*   | _ ->  *)
  (*     String.concat ["A world state of the form W<W> is expected, "; *)
  (*                    "but a given world state is of the form W, W."] *)
  (*     |! wrap_err *)

  (* let ext_ws_mpair_exn ws = ext_ws_mpair ws |! simpl_unwrap *)
  (* let ext_ws_apair_exn ws = ext_ws_apair ws |! simpl_unwrap *)

  let forward rule prem =
    try
      raise NotImplemented
    with e -> exn_wrap_err ~msg:(Error.fails "SBBI.forward") e


  let apply_split split seq =
    let tc2, tc_err = diff_list seq.WSeq.tcontext split.selected_tc in
    let fc2, fc_err = diff_list seq.WSeq.fcontext split.selected_fc in
    let wc1, wc2 = List.partition seq.WSeq.wcontext ~f: function 
      | WSeq.Mpair (seq1, seq2)
      | WSeq.Apair (seq1, seq2) -> List.mem (seq1.WSeq.world, seq2.WSeq.world) split.selected_wc in
    if tc_err <> [] then
      wrap_err "Some desired states do not exist in the tcontext"
    else if fc_err <> [] then
      wrap_err "Some desired false-props do not exist in the tcontext"
    (* We assume that ''seq'' is valid *)
    else if List.length wc1 <> List.length split.selected_wc then
      wrap_err "Some desired wstates do not exist in the tcontext"
    else
      wrap (
        WSeq.create ~tc:split.selected_tc ~fc:split.selected_fc ~wc:wc1 seq.WSeq.world,
        WSeq.create ~tc:tc2 ~fc:fc2 ~wc:wc2 seq.WSeq.world)

  let wrap_p_one seq = wrap (POne seq)
  let wrap_p_two (seq1, seq2) = wrap (PTwo (seq1, seq2))

  let backward rule seq = 
    try begin
      match rule with
      | Init -> begin
        match seq.WSeq.tcontext, seq.WSeq.fcontext, seq.WSeq.wcontext with
        | [WSeq.Prop prop_a], [prop_b], [] when prop_a = prop_b -> wrap PUnit
        | _, _, _::_ -> wrap_err "World context is not empty." |! simpl_unwrap
        | _ -> wrap_err "Both sides must be singltons and same with each other." |! simpl_unwrap
      end

      | TopL -> 
        seq
        |! WSeq.remove_tc_prop Prop.Top
          >> wrap_p_one
          
      | TopR -> begin
        match seq.WSeq.tcontext, seq.WSeq.fcontext, seq.WSeq.wcontext with
        | [], [Prop.Top], [] -> wrap PUnit
        | _::_, _, _ -> wrap_err "tcontext is not empty." |! simpl_unwrap
        | _, _, _::_ -> wrap_err "World context is not empty." |! simpl_unwrap
        | _ -> wrap_err "Other errors." |! simpl_unwrap
      end

      | BotL -> begin
        match seq.WSeq.tcontext, seq.WSeq.fcontext, seq.WSeq.wcontext with
        | [WSeq.Prop Prop.Bot], [], [] -> wrap PUnit
        | _, _::_, _ -> wrap_err "fcontext is not empty." |! simpl_unwrap
        | _, _, _::_ -> wrap_err "World context is not empty." |! simpl_unwrap
        | _ -> wrap_err "Other errors..." |! simpl_unwrap
      end

      | BotR -> 
        seq
        |! WSeq.remove_fc Prop.Bot
          >> wrap_p_one

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

      | AndR (Prop.And (prop_a, prop_b) as and_prop, split) ->
        let left_seq, right_seq = 
          seq
          |! WSeq.remove_fc and_prop
            >> apply_split split
          |! simpl_unwrap in
        (left_seq
         |! WSeq.add_fc prop_a
         |! unwrap "Add prop_A failed", (* unlikely failed *)
         right_seq
         |! WSeq.add_fc prop_b
         |! unwrap "Add prop_B failed") (* unlikely failed *)
        |! wrap_p_two

      | OrL (Prop.Or (prop_a, prop_b) as or_prop, split) ->
        let left_seq, right_seq = 
          seq
          |! WSeq.remove_tc_prop or_prop
            >> apply_split split
          |! simpl_unwrap in
        (left_seq
         |! WSeq.add_tc_prop prop_a
         |! unwrap "Add prop_A failed",
         right_seq
         |! WSeq.add_tc_prop prop_b
         |! unwrap "Add prop_B failed")
        |! wrap_p_two

      | OrR (Prop.Or (prop_a, prop_b) as or_prop) -> 
        seq 
        |! WSeq.remove_fc or_prop
          >> WSeq.add_fc prop_a
          >> WSeq.add_fc prop_b
          >> wrap_p_one

      | ImplyL (Prop.Imply (prop_a, prop_b) as imply_prop, split) ->
        let left_seq, right_seq = 
          seq 
          |! WSeq.remove_tc_prop imply_prop 
            >> apply_split split
          |! simpl_unwrap in
        (left_seq
         |! WSeq.add_fc prop_a,
         right_seq
         |! WSeq.add_tc_prop prop_b)
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

      | UnitR -> begin
        match seq.WSeq.tcontext, seq.WSeq.fcontext, seq.WSeq.wcontext with
        | [WSeq.Mzero], [Prop.Unit], [] -> wrap PUnit
        | _, _, _::_ -> wrap_err "World context is not empty." |! simpl_unwrap
        | _ -> wrap_err "Both sides must be singltons and ..." |! simpl_unwrap
      end

      | StarL ((Prop.Star (prop_a, prop_b) as star_prop), (w1, w2)) ->
        seq 
        |! WSeq.remove_tc_prop star_prop
          >> WSeq.add_wc_mpair (WSeq.create ~tc:[WSeq.Prop prop_a] w1, WSeq.create ~tc:[WSeq.Prop prop_b] w2)
          >> wrap_p_one

      | StarR -> begin
        match seq.WSeq.tcontext, seq.WSeq.fcontext, seq.WSeq.wcontext with
        | [], [Prop.Star (prop_a, prop_b)], [WSeq.Mpair (left_seq, right_seq)] ->
          (left_seq
           |! WSeq.add_fc prop_a,
           right_seq
           |! WSeq.add_fc prop_b)
          |! merge_result_pair
            >> wrap_p_two
        | _ -> wrap_err ("Not a proper sequent") |! simpl_unwrap
      end
            
      | WandL -> begin
        match seq.WSeq.tcontext, seq.WSeq.fcontext, seq.WSeq.wcontext with
        | [WSeq.Prop (Prop.Wand (prop_a, prop_b))], [], [WSeq.Apair (left_seq, right_seq)] ->
          (left_seq
           |! WSeq.add_fc prop_a,
           right_seq
           |! WSeq.add_tc_prop prop_b)
          |! merge_result_pair
            >> wrap_p_two
        | _ -> wrap_err ("Not a proper sequent") |! simpl_unwrap
      end

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

      | WeakL (WSeq.Prop prop) ->
        seq
        |! WSeq.remove_tc_prop prop
          >> wrap_p_one

      | WeakL (WSeq.Mzero) ->
        seq
        |! WSeq.remove_tc_mzero
          >> wrap_p_one

      | WeakR (prop) ->
        seq
        |! WSeq.remove_fc prop
          >> wrap_p_one

      | WeakW wpair -> begin
        match WSeq.exists_wc_mpair wpair seq with
        | Ok _ -> WSeq.remove_wc_mpair wpair seq >> wrap_p_one
        | _ -> WSeq.remove_wc_apair wpair seq >> wrap_p_one
      end

      | ContraL (WSeq.Prop prop) ->
        WSeq.exists_tc_prop prop seq |! simpl_unwrap;
        seq
        |! WSeq.add_tc_prop prop
          >> wrap_p_one

      | ContraL (WSeq.Mzero) ->
        WSeq.exists_tc_mzero seq |! simpl_unwrap;
        seq
        |! WSeq.add_tc_mzero
          >> wrap_p_one

      | ContraR (prop) ->
        WSeq.exists_fc prop seq |! simpl_unwrap;
        seq
        |! WSeq.add_fc prop
          >> wrap_p_one

      | ContraW (w1, w2, rename) -> begin
        (* (\* Renamings are valid? *\) *)
        Map.data rename 
        |! List.exn_if_dup ~compare:World.compare ~context:"Renamings' results are not distinct.(ContraW)" ~to_sexp:World.sexp_of_t;
        (* Convert! *)
        let world_find = function
          | WSeq.Mpair (seq1,seq2) 
          | WSeq.Apair (seq1,seq2) -> World.eq w1 seq1.WSeq.world && World.eq w2 seq2.WSeq.world in
        let wstate, _  = WSeq.pick_wc world_find seq |! simpl_unwrap in
        match wstate with
        | WSeq.Mpair (seq1, seq2) ->
          let seq1' = WSeq.apply_rename rename seq1 |! simpl_unwrap in
          let seq2' = WSeq.apply_rename rename seq2 |! simpl_unwrap in
          seq
          |! WSeq.add_wc_mpair (seq1', seq2')
            >> wrap_p_one
        | WSeq.Apair (seq1, seq2) -> 
          let seq1' = WSeq.apply_rename rename seq1 |! simpl_unwrap in
          let seq2' = WSeq.apply_rename rename seq2 |! simpl_unwrap in
          seq
          |! WSeq.add_wc_apair (seq1', seq2')
            >> wrap_p_one
      end

      | Comm wc_mpair ->
        let (wl, wr), base_seq  = WSeq.pick_wc_mpair wc_mpair seq |! simpl_unwrap in
        base_seq
        |! WSeq.add_wc_mpair (wr, wl) 
          >> wrap_p_one

      | Assoc (outer, w_new) -> begin
        let (w', w3), base_seq  = WSeq.pick_wc_mpair outer seq |! unwrap "Cannot find outer" in
        match w'.WSeq.tcontext, w'.WSeq.fcontext, w'.WSeq.wcontext with
        | [], [], [WSeq.Mpair(w1, w2)] ->
          base_seq
          |! WSeq.add_wc_mpair (w1, WSeq.create ~wc:[WSeq.Mpair(w2, w3)] w_new)
            >> wrap_p_one
        | _ -> wrap_err "w' is not Mpair world" |! simpl_unwrap
      end

      | ZeroU (split, (w_new, w_new')) ->
        let left_seq, right_seq = 
          seq 
          |! apply_split split
          |! unwrap "Split failed" in
        left_seq
        |! WSeq.add_wc_mpair ({right_seq with WSeq.world = w_new}, WSeq.create ~tc:[WSeq.Mzero] w_new')
          >> wrap_p_one
      (* right_seq rename... need to revise *)

      | ZeroD (wc_mpair) -> begin
        let (wl, wr), base_seq  = WSeq.pick_wc_mpair wc_mpair seq |! simpl_unwrap in
        match wr.WSeq.tcontext, wr.WSeq.fcontext, wr.WSeq.wcontext with
        | [WSeq.Mzero], [], [] -> 
          WSeq.merge base_seq wl
          >> wrap_p_one
        | _ -> wrap_err "wr is not Mzero world" |! simpl_unwrap
      end
            
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
    | Init -> "\\RSBinit"
    | TopL -> "\\RSBtopleft"
    | TopR -> "\\RSBtopright"
    | BotL -> "\\RSBbotleft"
    | BotR -> "\\RSBbotright"
    | NegL _ -> "\\RSBnegleft"
    | NegR _ -> "\\RSBnegright"
    | AndL _ -> "\\RSBandleft"
    | AndR _ -> "\\RSBandright"
    | OrL _ -> "\\RSBorleft"
    | OrR _ -> "\\RSBorright"
    | ImplyL _ -> "\\RSBimplyleft"
    | ImplyR _ -> "\\RSBimplyright"
    | UnitL -> "\\RSBunitleft"
    | UnitR -> "\\RSBunitright"
    | StarL _ -> "\\RSBstarleft"
    | StarR _ -> "\\RSBstarright"
    | WandL _ -> "\\RSBwandleft"
    | WandR _ -> "\\RSBwandright"
    | TC _ -> "\\RSBdown"
    | TP _ -> "\\RSBup"
    | WeakL _ -> "\\RSBweakeningleft"
    | WeakR _ -> "\\RSBweakeningright"
    | WeakW _ -> "\\RSBweakeningleft"
    | ContraL _ -> "\\RSBcontractionleft"
    | ContraR _ -> "\\RSBcontractionright"
    | ContraW _ -> "\\RSBcontractionleft"
    | Comm _ -> "\\RSBcomm"
    | Assoc _ -> "\\RSBassoc"
    | ZeroU _ -> "\\RSBmultzeroup"
    | ZeroD _ -> "\\RSBmultzerodown"


  let no_highlight = fun _ -> false
  let tc_eq_prop prop1 wstate2 = WSeq.Prop prop1 = wstate2
  let tc_eq_mzero wstate2 = WSeq.Mzero = wstate2
  let fc_eq prop1 prop2 = prop1 = prop2

  let seq_to_tex = function
    | Init -> 
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | TopL ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop Prop.Top)
        ~fc_highlight:no_highlight
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
    | BotR ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq Prop.Bot)
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
    | AndR (prop, _) ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop)
    | OrL (prop, _) ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:(tc_eq_prop prop)
        ~fc_highlight:no_highlight
    | OrR prop ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop)
    | ImplyL (prop, _) ->
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
    | StarR ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | WandL ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
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
    | WeakL st ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:((=) st)
        ~fc_highlight:no_highlight
    | WeakR prop ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop)
    | WeakW (w1,w2) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | ContraL s ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:((=) s)
        ~fc_highlight:no_highlight
    | ContraR prop ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:(fc_eq prop)
    | ContraW (w1, w2, rn) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | Comm (w1,w2) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | Assoc ((w1,w2), _) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | ZeroU _ ->
      WSeq.to_tex 
        ~w_highlight:no_highlight
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
    | ZeroD (w1,w2) ->
      WSeq.to_tex 
        ~w_highlight:(fun x -> World.eq x w1 || World.eq x w2)
        ~tc_highlight:no_highlight
        ~fc_highlight:no_highlight
end

module Build =
struct
  type desc = 
  | Init of World.t * Prop.t
  | TopL 
  | TopR of World.t
  | BotL of World.t
  | BotR
  | NegL of Prop.t
  | NegR of Prop.t
  | AndL of Prop.t
  | AndR of Prop.t
  | OrL of Prop.t
  | OrR of Prop.t
  | ImplyL of Prop.t
  | ImplyR of Prop.t
  | UnitL  
  | UnitR of World.t
  | StarL of Prop.t * (World.t * World.t)
  | StarR of World.t * Prop.t
  | WandL of World.t * Prop.t
  | WandR of Prop.t * (World.t * World.t)
  | TC of (World.t * World.t)
  | TP of (World.t * World.t)
  | WeakL of WSeq.state
  | WeakR of Prop.t
  | WeakW of WSeq.wstate
  | ContraL of WSeq.state
  | ContraR of Prop.t
  | ContraW of (World.t * World.t) * World.rename
  | Comm of (World.t * World.t)
    (* Assoc ((w_1, w_new), w_1n2) *)
  | Assoc of ((World.t * World.t) * World.t)
  | ZeroU of (World.t * World.t)
  | ZeroD of (World.t * World.t * Rule.split)
  with sexp

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

  let rec worlds_in_s { WSeq.world = w; WSeq.wcontext = wc } =
    Set.add (Set.union_list (List.map ~f:worlds_in_ws wc)) w

  and worlds_in_ws = function
    | WSeq.Mpair (wseq_1, wseq_2) | WSeq.Apair (wseq_1, wseq_2) -> 
      Set.union (worlds_in_s wseq_1) (worlds_in_s wseq_2)

  let filter_rn ws rn =
    let wset = worlds_in_ws ws in
    Map.filter ~f:(fun ~key:w ~data -> Set.mem wset w) rn

  let filter_rn_s s rn =
    let wset = worlds_in_s s in
    Map.filter ~f:(fun ~key:w ~data -> Set.mem wset w) rn

  (** Auxililary functions for the forward function *)
  let forward_fails case_id prem =
    String.concat [Error.fails case_id; "\n";
                   "The following premise is given:"; "\n";
                   Rule.sexp_of_premise prem |! Sexp.to_string_hum]

  let forward_init_exn (w, prop) prem =
    try
      let () = Rule.match_prem_unit_exn prem in
      Rule.Init, WSeq.create w ~tc:[WSeq.Prop prop] ~fc:[prop]
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_init_left" prem) e

  let forward_top_left_exn prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      Rule.TopL, WSeq.add_tc_prop_exn Prop.Top wseq
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_top_left" prem) e

  let forward_top_right_exn w prem =
    try
      let () = Rule.match_prem_unit_exn prem in
      Rule.TopR, WSeq.create w ~fc:[Prop.Top]
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_top_right" prem) e

  let forward_bot_left_exn w prem =
    try
      let () = Rule.match_prem_unit_exn prem in
      Rule.BotL, WSeq.create w ~tc:[WSeq.Prop Prop.Bot]
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_bot_left" prem) e

  let forward_bot_right_exn prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      Rule.BotR, WSeq.add_fc_exn Prop.Bot wseq
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_bot_right" prem) e

  let forward_neg_left_exn prop prem =
    try
      let prop_A = Prop.match_prop_neg_exn prop in
      let wseq = Rule.match_prem_one_exn prem in
      Rule.NegL prop,
      WSeq.add_tc_prop_exn (Prop.Neg prop_A) wseq 
      |! WSeq.remove_fc_exn prop_A 
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_neg_left" prem) e

  let forward_neg_right_exn prop prem =
    try
      let prop_A = Prop.match_prop_neg_exn prop in
      let wseq = Rule.match_prem_one_exn prem in
      Rule.NegR prop,
      WSeq.add_fc_exn (Prop.Neg prop_A) wseq 
      |! WSeq.remove_tc_prop_exn prop_A 
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_neg_right" prem) e

  let forward_and_left_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_and_exn prop in
      let wseq = Rule.match_prem_one_exn prem in
      Rule.AndL prop,
      WSeq.add_tc_prop_exn (Prop.And (prop_A, prop_B)) wseq 
      |! WSeq.remove_tc_prop prop_A 
      |! unwrap "Can't remove the proposition A."
      |! WSeq.remove_tc_prop prop_B
      |! unwrap "Can't remove the proposition B."
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_and_left" prem) e

  let forward_and_right_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_and_exn prop in
      let wseq_A, wseq_B = Rule.match_prem_two_exn prem in
        (* Compute the goal sequent *)
      let { WSeq.tcontext = tc_A; WSeq.fcontext = fc_A; WSeq.wcontext = wc_A; } as wseq_A' = 
        WSeq.remove_fc prop_A wseq_A |! unwrap "Can't remove the proposition A." in
      let wseq_B' = WSeq.remove_fc prop_B wseq_B |! unwrap "Can't remove the proposition B." in      
      let wseq = WSeq.merge wseq_A' wseq_B' |! simpl_unwrap in
        (* Compute the split *)
      let split = 
        { Rule.selected_tc = tc_A;
          Rule.selected_fc = fc_A; 
          Rule.selected_wc = List.map ~f:get_names wc_A }
      in
      Rule.AndR (prop, split), WSeq.add_fc_exn (Prop.And (prop_A, prop_B)) wseq
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_and_right" prem) e

  let forward_or_left_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_or_exn prop in
      let wseq_A, wseq_B = Rule.match_prem_two_exn prem in
        (* Compute the goal sequent *)
      let { WSeq.tcontext = tc_A; WSeq.fcontext = fc_A; WSeq.wcontext = wc_A; } as wseq_A' = 
        WSeq.remove_tc_prop prop_A wseq_A |! unwrap "Can't remove the proposition A." in
      let wseq_B' = WSeq.remove_tc_prop prop_B wseq_B |! unwrap "Can't remove the proposition B." in      
      let wseq = WSeq.merge wseq_A' wseq_B' |! simpl_unwrap in
        (* Compute the split *)
      let split = 
        { Rule.selected_tc = tc_A;
          Rule.selected_fc = fc_A; 
          Rule.selected_wc = List.map ~f:get_names wc_A }
      in
      Rule.OrL (prop, split), WSeq.add_tc_prop_exn (Prop.Or (prop_A, prop_B)) wseq
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_or_left" prem) e

  let forward_or_right_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_or_exn prop in
      let wseq = Rule.match_prem_one_exn prem in
      Rule.OrR prop,
      WSeq.add_fc_exn (Prop.Or (prop_A, prop_B)) wseq 
      |! WSeq.remove_fc prop_A 
      |! unwrap "Can't remove the proposition A."
      |! WSeq.remove_fc prop_B
      |! unwrap "Can't remove the proposition B."
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_or_right" prem) e

  let forward_imply_left_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_imply_exn prop in
      let wseq_A, wseq_B = Rule.match_prem_two_exn prem in
        (* Compute the goal sequent *)
      let { WSeq.tcontext = tc_A; WSeq.fcontext = fc_A; WSeq.wcontext = wc_A; } as wseq_A' = 
        WSeq.remove_fc prop_A wseq_A |! unwrap "Can't remove the proposition A." in
      let wseq_B' = WSeq.remove_tc_prop prop_B wseq_B |! unwrap "Can't remove the proposition B." in      
      let wseq = WSeq.merge wseq_A' wseq_B' |! simpl_unwrap in
        (* Compute the split *)
      let split = 
        { Rule.selected_tc = tc_A;
          Rule.selected_fc = fc_A; 
          Rule.selected_wc = List.map ~f:get_names wc_A }
      in
      Rule.ImplyL (prop, split), WSeq.add_tc_prop_exn (Prop.Imply (prop_A, prop_B)) wseq
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_imply_left" prem) e

  let forward_imply_right_exn prop prem =
    try
      let prop_A, prop_B = Prop.match_prop_imply_exn prop in
      let wseq = Rule.match_prem_one_exn prem in
      Rule.ImplyR prop,
      WSeq.add_fc_exn (Prop.Imply (prop_A, prop_B)) wseq 
      |! WSeq.remove_tc_prop prop_A 
      |! unwrap "Can't remove the proposition A."
      |! WSeq.remove_fc prop_B
      |! unwrap "Can't remove the proposition B."
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_imply_right" prem) e

  let forward_unit_left_exn prem =
    try
      let wseq = Rule.match_prem_one prem |! simpl_unwrap in
      Rule.UnitL,
      WSeq.add_tc_prop_exn Prop.Unit wseq 
      |! WSeq.remove_tc_mzero_exn    
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_unit_left" prem) e

  let forward_unit_right_exn w prem =
    try
      let () = Rule.match_prem_unit_exn prem in
      Rule.UnitR,
      WSeq.create w ~tc:[WSeq.Mzero] ~fc:[Prop.Unit]
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_unit_right" prem) e

  let forward_star_left_exn (prop, (w_A, w_B)) prem =
    try
      let prop_A, prop_B = Prop.match_prop_star prop |! simpl_unwrap in
      let wseq = Rule.match_prem_one_exn prem in
      let _, wseq_r = WSeq.pick_wc_exn (mpair_with_worlds w_A w_B) wseq in
      Rule.StarL (prop, (w_A, w_B)),
      WSeq.add_tc_prop_exn (Prop.Star (prop_A, prop_B)) wseq_r
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_star_left" prem) e

  let forward_star_right_exn (w, prop) prem =
    try
      let prop_A, prop_B = Prop.match_prop_star_exn prop in
      let wseq_A, wseq_B = Rule.match_prem_two_exn prem in
      let wseq_A' = WSeq.remove_fc prop_A wseq_A |! unwrap "Can't remove proposition A." in
      let wseq_B' = WSeq.remove_fc prop_B wseq_B |! unwrap "Can't remove proposition B." in
      Rule.StarR, WSeq.create w ~fc:[prop] ~wc:[WSeq.Mpair (wseq_A', wseq_B')]
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_star_right" prem) e

  let forward_wand_left_exn (w, prop) prem =
    try
      let prop_A, prop_B = Prop.match_prop_wand_exn prop in
      let wseq_A, wseq_B = Rule.match_prem_two_exn prem in
      let wseq_A' = WSeq.remove_fc prop_A wseq_A |! unwrap "Can't remove proposition A." in
      let wseq_B' = WSeq.remove_tc_prop prop_B wseq_B |! unwrap "Can't remove proposition B." in
      Rule.WandL, WSeq.create w ~tc:[WSeq.Prop prop] ~wc:[WSeq.Apair (wseq_A', wseq_B')]
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_wand_left" prem) e

  let forward_wand_right_exn (prop, (w_A, w_B)) prem =
    try
      let prop_A, prop_B = Prop.match_prop_wand prop |! simpl_unwrap in
      let wseq = Rule.match_prem_one_exn prem in
      let _, wseq_r = WSeq.pick_wc_exn (apair_with_worlds w_A w_B) wseq in
      Rule.WandR (prop, (w_A, w_B)),
      WSeq.add_fc_exn (Prop.Wand (prop_A, prop_B)) wseq_r
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_wand_right" prem) e

  let forward_tc_exn (w_c1, w_c2) prem =
    try
      let wseq = Rule.match_prem_one_exn prem  in
      let (wseq_c2, wseq'), wseq_c1 = 
        WSeq.pick_wc (apair_with_sibling w_c2) wseq 
        |! simpl_unwrap 
        |! Tuple.T2.map1 ~f:match_ws_apair_exn in
      Rule.TC (w_c1, w_c2),
      WSeq.add_wc_mpair_exn (wseq_c1, wseq_c2) wseq'
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_tc" prem) e

  let forward_tp_exn (w_s, w_p) prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      let (wseq', wseq_s), wseq_p =
        WSeq.pick_wc_exn (mpair_with_rchild w_s) wseq
        |! Tuple.T2.map1 ~f:match_ws_mpair_exn in
      Rule.TP (w_s, w_p),
      WSeq.add_wc_apair_exn (wseq_s, wseq_p) wseq'
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_tp" prem) e

  let forward_weakening_left_exn s prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      Rule.WeakL s,
      match s with
      | WSeq.Prop prop -> WSeq.add_tc_prop_exn prop wseq
      | WSeq.Mzero -> WSeq.add_tc_mzero_exn wseq
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_weakening_left" prem) e

  let forward_weakening_right_exn prop prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      Rule.WeakR prop,
      WSeq.add_fc_exn prop wseq
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_weakening_right" prem) e

  let forward_weakening_wstate_exn ws prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      match ws with
      | WSeq.Mpair (wseq_1, wseq_2) ->
        let { WSeq.world = w_1 } = wseq_1 in
        let { WSeq.world = w_2 } = wseq_2 in
        Rule.WeakW (w_1, w_2),
        WSeq.add_wc_mpair_exn (wseq_1, wseq_2) wseq
      | WSeq.Apair (wseq_1, wseq_2) ->
        let { WSeq.world = w_1 } = wseq_1 in
        let { WSeq.world = w_2 } = wseq_2 in
        Rule.WeakW (w_1, w_2),
        WSeq.add_wc_apair_exn (wseq_1, wseq_2) wseq
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_weakening_wstate" prem) e
      
  let forward_contraction_left_exn s prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      Rule.ContraL s,
      match s with
      | WSeq.Prop prop -> WSeq.remove_tc_prop_exn prop wseq
      | WSeq.Mzero -> WSeq.remove_tc_mzero_exn wseq
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_contra_left" prem) e

  let forward_contraction_right_exn prop prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      Rule.ContraR prop, WSeq.remove_fc_exn prop wseq
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_contra_right" prem) e

  let forward_contraction_wstate_exn ((w_1, w_2), rn) prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      let w_1' = World.rename rn w_1 |! unwrap "Can't find w_1." in
      let w_2' = World.rename rn w_2 |! unwrap "Can't find w_2." in
      let _, wseq_r = WSeq.pick_wc_exn (match_ws_with_worlds w_1' w_2') wseq in
      let ws, _ = WSeq.pick_wc_exn (match_ws_with_worlds w_1 w_2) wseq in
      Rule.ContraW (w_1, w_2, filter_rn ws rn), wseq_r
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_contra_wstate" prem) e

  let forward_comm_exn (w_l, w_r) prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      let (wseq_r, wseq_l), wseq' =
        WSeq.pick_wc_exn (mpair_with_worlds w_r w_l) wseq        
        |! Tuple.T2.map1 ~f:match_ws_mpair_exn in
      Rule.Comm (w_l, w_r),
      WSeq.add_wc_mpair_exn (wseq_l, wseq_r) wseq'
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_comm" prem) e

  let forward_assoc_exn ((w_1, w_new), w_1n2) prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      let (wseq_1, wseq_new), wseq' = 
        WSeq.pick_wc_exn (mpair_with_worlds w_1 w_new) wseq 
        |! Tuple.T2.map1 ~f:match_ws_mpair_exn in
      let (wseq_2, wseq_3), _ = 
        WSeq.pick_wc_exn (fun _ -> true) wseq_new 
        |! Tuple.T2.map1 ~f:match_ws_mpair_exn in
      let wseq_1n2 = WSeq.create w_1n2 ~wc:[WSeq.Mpair (wseq_1, wseq_2)] in
      Rule.Assoc ((w_1n2, wseq_3.WSeq.world), w_new),
      WSeq.add_wc_mpair_exn (wseq_1n2, wseq_3) wseq'
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_assoc" prem) e

  let forward_zero_up_exn (w_l, w_r) prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      let (wseq_l, wseq_r), wseq' =
        WSeq.pick_wc_exn (mpair_with_worlds w_l w_r) wseq
        |! Tuple.T2.map1 ~f:match_ws_mpair_exn in
        (* Compute the split *)
      let { WSeq.tcontext = tc; WSeq.fcontext = fc; WSeq.wcontext = wc } = wseq' in
      let split = 
        { Rule.selected_tc = tc;
          Rule.selected_fc = fc; 
          Rule.selected_wc = List.map ~f:get_names wc }
        (* Compute the rule & goal sequent *)
      in Rule.ZeroU (split, (w_l, w_r)), WSeq.merge wseq' wseq_l |! simpl_unwrap
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_zero_up" prem) e

  let forward_zero_down_exn (w_l, w_r, sp) prem =
    try
      let wseq = Rule.match_prem_one_exn prem in
      let wseq_s, wseq_p = Rule.apply_split sp wseq |! simpl_unwrap in
      Rule.ZeroD (w_l, w_r),
      WSeq.add_wc_mpair_exn ({ wseq_s with WSeq.world = w_l }, WSeq.create w_r ~tc:[WSeq.Mzero]) wseq_p
    with e -> exn_reraise ~msg:(forward_fails "SBBI.forward_zero_down" prem) e

  let forward desc prem = 
    try
      let seq =
        match desc with
        | Init (w, prop) -> forward_init_exn (w, prop) prem
        | TopL -> forward_top_left_exn prem
        | TopR w -> forward_top_right_exn w prem
        | BotL w -> forward_bot_left_exn w prem
        | BotR -> forward_bot_right_exn prem
        | NegL prop -> forward_neg_left_exn prop prem
        | NegR prop -> forward_neg_right_exn prop prem
        | AndL prop -> forward_and_left_exn prop prem
        | AndR prop -> forward_and_right_exn prop prem
        | OrL prop -> forward_or_left_exn prop prem
        | OrR prop -> forward_or_right_exn prop prem
        | ImplyL prop -> forward_imply_left_exn prop prem
        | ImplyR prop -> forward_imply_right_exn prop prem
        | UnitL -> forward_unit_left_exn prem
        | UnitR w -> forward_unit_right_exn w prem
        | StarL (prop, worlds) -> forward_star_left_exn (prop, worlds) prem
        | StarR (w, prop) -> forward_star_right_exn (w, prop) prem
        | WandL (w, prop) -> forward_wand_left_exn (w, prop) prem
        | WandR (prop, worlds) -> forward_wand_right_exn (prop, worlds) prem
        | TC worlds -> forward_tc_exn worlds prem
        | TP worlds -> forward_tp_exn worlds prem
        | WeakL s -> forward_weakening_left_exn s prem           
        | WeakR prop -> forward_weakening_right_exn prop prem
        | WeakW ws -> forward_weakening_wstate_exn ws prem
        | ContraL s -> forward_contraction_left_exn s prem
        | ContraR prop -> forward_contraction_right_exn prop prem
        | ContraW (ws, rn) -> forward_contraction_wstate_exn (ws, rn) prem
        | Comm worlds -> forward_comm_exn worlds prem
        | Assoc worlds -> forward_assoc_exn worlds prem
        | ZeroU worlds -> forward_zero_up_exn worlds prem
        | ZeroD (w_l, w_r, sp) -> forward_zero_down_exn (w_l, w_r, sp) prem
      in wrap seq
    with e -> exn_wrap_err ~msg:(Error.fails "SBBI.forward") e
end

module Proof = ProofFn (Rule)

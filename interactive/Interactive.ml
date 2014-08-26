(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

(* Controller *)
module Command :
sig
  type tactic = Proof_type.rule

  type t =
  | Open of Prop.t
  | Restart
  | Close
  | Apply of tactic
  | Undo
  | Auto of int
  | Trivial
  | Next_subgoal
  | Prev_subgoal
  | Next_branch
  | Prev_branch
  | Fork                                (* debugging *)
  | Print_history                       (* debugging *)
  | Help
  | Quit
  | Save of string
  | Show_all
  | Show_visible
  | Show_toggle
  | Save_seq_pic of string

  val from_string : string -> t result
  val from_string_exn : string -> t
end
=
struct
  type tactic = Proof_type.rule

  type t =
  | Open of Prop.t
  | Restart
  | Close
  | Apply of tactic
  | Undo
  | Auto of int
  | Trivial
  | Next_subgoal
  | Prev_subgoal
  | Next_branch
  | Prev_branch
  | Fork                                (* debugging *)
  | Print_history                       (* debugging *)
  | Help
  | Quit
  | Save of string
  | Show_all
  | Show_visible
  | Show_toggle
  | Save_seq_pic of string

  open Genlex

  let lexer = make_lexer [
    "("; ")"; "T"; "F"; "I"; "!"; "/\\"; "\\/"; "->"; "-*"; "*";
    "open";
    "restart";
    "close";
    "apply";
    "undo";
    "auto";
    "trivial";
    "next_goal";
    "prev_goal";
    "next_branch";
    "prev_branch";
    "save";
    "fork";
    "history";
    "help";
    "quit";
    "Init"; "TopR"; "BotL"; "NegL"; "NegR";
    "AndL"; "AndR"; "OrL"; "OrR"; "ImplyL";
    "ImplyR"; "UnitL"; "UnitR"; "StarL"; "WandR";
    "Comm"; "ZeroU"; "ZeroD"; "StarR"; "WandL";
    "Assoc";
    "goal"; "all"; "show"; "visible"; "toggle";
  ]

  let rec parse_atom_prop = parser
    | [< 'Ident s >] -> Prop.Atom s
    | [< 'Kwd "T" >] -> Prop.Top
    | [< 'Kwd "F" >] -> Prop.Bot
    | [< 'Kwd "I" >] -> Prop.Unit
    | [< 'Kwd "("; prop_A = parse_prop; 'Kwd ")" >] -> prop_A

  and parse_neg_prop = parser
    | [< 'Kwd "!"; prop_A = parse_neg_prop >] -> Prop.Neg prop_A
    | [< prop_A = parse_atom_prop >] -> prop_A

  and parse_and_prop = parser
    | [< prop_A = parse_and_prop_left (fun a -> a) >] -> prop_A
      
  and parse_and_prop_left cont = parser
    | [< prop_A = parse_neg_prop; prop_B = parse_and_prop_aux (cont prop_A) >] -> prop_B
      
  and parse_and_prop_aux prop_A = parser
    | [< 'Kwd "/\\"; prop = parse_and_prop_left (fun b -> Prop.And(prop_A,b)) >] -> prop
    | [< 'Kwd "*"; prop = parse_and_prop_left (fun b -> Prop.Star(prop_A,b)) >] -> prop
    | [< >] -> prop_A

  and parse_or_prop = parser
    | [< prop_A = parse_or_prop_left (fun a -> a) >] -> prop_A

  and parse_or_prop_left cont = parser
    | [< prop_A = parse_and_prop; prop_B = parse_or_prop_aux (cont prop_A) >] -> prop_B

  and parse_or_prop_aux prop_A = parser
    | [< 'Kwd "\\/"; prop = parse_or_prop_left (fun b -> Prop.Or(prop_A,b)) >] -> prop
    | [< >] -> prop_A

  and parse_imply_prop = parser
    | [< prop_A = parse_or_prop; prop_A' = parse_imply_prop_aux prop_A >] -> prop_A'

  and parse_imply_prop_aux prop_A = parser
    | [< 'Kwd "->"; prop_B = parse_imply_prop >] -> Prop.Imply (prop_A, prop_B)
    | [< 'Kwd "-*"; prop_B = parse_imply_prop >] -> Prop.Wand (prop_A, prop_B)
    | [< >] -> prop_A

  and parse_prop = parser
    | [< prop_A = parse_imply_prop >] -> prop_A
    
  (* *)
  let rec parse_cmd = parser
    | [< 'Kwd "open"; prop = parse_prop >] -> Open prop
    | [< 'Kwd "restart" >] -> Restart
    | [< 'Kwd "close" >] -> Close
    | [< 'Kwd "undo" >] -> Undo
    | [< 'Kwd "apply"; tac = parse_apply_cmd >] -> Apply tac
    | [< 'Kwd "auto"; i = parser | [<'Int n >] -> n | [< >] -> 2 >] -> Auto i
    | [< 'Kwd "trivial" >] -> Trivial
    | [< 'Kwd "next_goal" >] -> Next_subgoal
    | [< 'Kwd "prev_goal" >] -> Prev_subgoal
    | [< 'Kwd "next_branch" >] -> Next_branch
    | [< 'Kwd "prev_branch" >] -> Prev_branch
    | [< 'Kwd "fork" >] -> Fork
    | [< 'Kwd "history" >] -> Print_history
    | [< 'Kwd "help" >] -> Help
    | [< 'Kwd "quit" >] -> Quit
    | [< 'Kwd "save"; save = parse_save_cmd>] -> save
    | [< 'Kwd "show"; show = parse_show_cmd >] -> show

  and parse_save_cmd = parser
    | [< 'String filename >] -> Save filename
    | [< 'Kwd "goal"; 'String filename >] -> Save_seq_pic filename

  and parse_show_cmd = parser
    | [< 'Kwd "all"  >] -> Show_all
    | [< 'Kwd "visible" >] -> Show_visible
    | [< 'Kwd "toggle" >] -> Show_toggle

  and parse_apply_cmd = parser
    | [< 'Kwd "Init"; 'Int n; 'Int n'; 'Int n'' >] -> Proof_type.Init (n, n', n'')
    | [< 'Kwd "TopR"; 'Int n; 'Int n' >] -> Proof_type.TopR (n, n')
    | [< 'Kwd "BotL"; 'Int n; 'Int n' >] -> Proof_type.BotL (n, n')
    | [< 'Kwd "NegL"; 'Int n; 'Int n' >] -> Proof_type.NegL (n, n')
    | [< 'Kwd "NegR"; 'Int n; 'Int n' >] -> Proof_type.NegR (n, n')
    | [< 'Kwd "AndL"; 'Int n; 'Int n' >] -> Proof_type.AndL (n, n')
    | [< 'Kwd "AndR"; 'Int n; 'Int n' >] -> Proof_type.AndR (n, n')
    | [< 'Kwd "OrL"; 'Int n; 'Int n' >] -> Proof_type.OrL (n, n')
    | [< 'Kwd "OrR"; 'Int n; 'Int n' >] -> Proof_type.OrR (n, n')
    | [< 'Kwd "ImplyL"; 'Int n; 'Int n' >] -> Proof_type.ImplyL (n, n')
    | [< 'Kwd "ImplyR"; 'Int n; 'Int n' >] -> Proof_type.ImplyR (n, n')
    | [< 'Kwd "UnitL"; 'Int n; 'Int n' >] -> Proof_type.UnitL (n, n')
    | [< 'Kwd "UnitR"; 'Int n; 'Int n' >] -> Proof_type.UnitR (n, n')
    | [< 'Kwd "StarL"; 'Int n; 'Int n' >] ->  Proof_type.StarL (n, n')
    | [< 'Kwd "WandR"; 'Int n; 'Int n' >] ->  Proof_type.WandR (n, n')
    | [< 'Kwd "Comm"; 'Int n; 'Int n' >] ->  Proof_type.Comm (n, n')
    | [< 'Kwd "ZeroU"; 'Int n >] ->  Proof_type.ZeroU n
    | [< 'Kwd "ZeroD"; 'Int n; 'Int n' >] ->  Proof_type.ZeroD (n, n')
    | [< 'Kwd "StarR"; 'Int n; 'Int n'; 'Int n'' >] -> Proof_type.StarR (n, n', n'')
    | [< 'Kwd "WandL" ; 'Int n; 'Int n'; 'Int n''>] -> Proof_type.WandL (n, n', n'')
    | [< 'Kwd "Assoc"; 'Int n; 'Int n'; 'Int n''>] -> Proof_type.Assoc (n, n', n'')
      
  let escape_neg str =
    Core.Core_string.split str ~on:'!'
    |! Core.Core_string.concat ~sep:" !"

  (* from_string : string -> cmd *)
  let from_string s =
    try
      escape_neg s |! Stream.of_string |! lexer |! parse_cmd |! wrap
    with
    | Stream.Failure -> wrap_err s
    | Stream.Error msg -> wrap_err msg

  let from_string_exn s = from_string s |! simpl_unwrap
end

(* Model *)
module Session :
sig
  val init : unit -> unit
    
  val start_fprop: fprop:Prop.t -> unit result

  val close : unit -> unit result

  val restart : unit -> unit result

  val get_goalseq : unit -> Seq.seq result

  val to_string : unit -> string

  val print_history : unit -> string

  val step : Command.tactic -> unit result

  val undo : unit -> unit result

  val auto : int -> unit result
    
  val trivial : unit -> unit result

  val fork: unit -> unit result

  val next_subgoal : unit -> unit result

  val prev_subgoal : unit -> unit result

  val next_branch : unit -> unit result

  val prev_branch : unit -> unit result

  val save: filename:string -> unit result

  val save_seq_pic: filename:string -> unit result

  val show_all: unit -> unit

  val show_visible: unit -> unit

  val show_toggle: unit -> unit

  val help_msg: unit -> string
end
=
struct

  module LCheck = ProofChecker.Make (LBBI)
  module CCheck = ProofChecker.Make (CSBBI)
  module SCheck = ProofChecker.Make (SBBI)

  module LWrite = ProofWriter.Make (LBBI)
  module CWrite = ProofWriter.Make (CSBBI)
  module SWrite = ProofWriter.Make (SBBI)

  type t = 
  | Idle
  | Ing of (Refiner.pftreestate * Refiner.pftreestate list * Refiner.pftreestate list) (* focused, next, prev_inv. ie. 3, 4::5, 2::1::0 *)
  | Qed of Refiner.pftreestate

  let show_hidden_worlds = ref false

  let st = ref Idle
  let lproof = ref None
  let cproof = ref None
  let sproof = ref None

  let init () = 
    st := Idle;
    lproof := None;
    cproof := None;
    sproof := None;
    show_hidden_worlds := false
      
  let start_fprop ~fprop =
    match !st with
    | Idle ->
      let base_w = World.get_fresh () in
      wrap (st := Ing (Refiner.mk_pftreestate (Seq.of_lseq (LSeq.create [base_w] ~fc:[fprop, base_w])), [], []))
    | _ ->
      wrap_err "Open fails: you are already working on a different session. Close it first."
        
  let close () =
    match !st with
    | Idle -> wrap_err "Close fails: there is no working session."
    | _ -> init () |! wrap

  let restart () =
    match !st with
    | Idle -> wrap_err "Restart fails: there is no working session."
    | Ing (t, _, _) | Qed t ->
      let t' = Refiner.top_of_tree t |! Refiner.top_goal_of_pftreestate |! Refiner.mk_pftreestate in
      init ();
      wrap (st := Ing (t', [], []))
        
  let get_goalseq () = 
    match !st with
    | Ing (t, _, _)
    | Qed t -> Refiner.top_goal_of_pftreestate t |! wrap
    | Idle -> wrap_err "get_goalseq fails: there is no working session."

  let to_string () = 
    match !st with
    | Ing (t, next, prev) -> 
      let nnext = List.length next in
      let nprev = List.length prev in
      let all = nnext + nprev + 1 in
      (if all = 1 then ""
       else sprintf "%d / %d branches" (nprev + 1) (nnext + nprev + 1)) 
      ^ "\n" ^ Refiner.pftreestate_to_string ~show_hidden:(!show_hidden_worlds) t
    | Qed t -> "Proof completed! Type 'save \"filename\"' to save the proof to the file \"filename\"."
    | Idle -> "Idle. Type 'open <PROPOSITION>' to start a session. ex) open A->A"

  let print_history () = 
    match !st with
    | Ing (t, _, _) 
    | Qed t ->
      (Refiner.top_of_tree t |! Refiner.pftreestate_to_string_simple)
    | Idle -> "Idle. Type 'open <PROPOSITION>' to start a session. ex) open A->A"

  let next_subgoal () = 
    match !st with
    | Idle -> wrap_err "next_goal fails: there is no working session."
    | Qed _ -> wrap_err "next_goal fails: there is no unproven subgoal."
    | Ing (t, next, prev) -> 
      try
        wrap (st := Ing (Refiner.next_unproven t, next, prev))
      with
      | Refiner.Not_found_pf _ -> 
        let t' = Refiner.top_of_tree t |! Refiner.first_unproven in
        wrap (st := Ing (t', next, prev))

  let prev_subgoal () = 
    match !st with
    | Idle -> wrap_err "prev_goal fails: there is no working session."
    | Qed _ -> wrap_err "prev_goal fails: there is no unproven subgoal."
    | Ing (t, next, prev) -> 
      try
        wrap (st := Ing (Refiner.prev_unproven t, next, prev))
      with
      | Refiner.Not_found_pf _ -> 
        let t' = Refiner.top_of_tree t |! Refiner.last_unproven in
        wrap (st := Ing (t', next, prev))

  let next_branch () = 
    match !st with
    | Idle -> wrap_err "next_branch fails: there is no working session."
    | Qed _ -> wrap_err "next_branch fails: there is no unproven subgoal."
    | Ing (t, [], []) -> wrap_err "next_branch fails: there is only one branch."
    | Ing (t, [], prev) -> begin
      match List.rev (t::prev) with
      | [] -> assert false
      | t'::next -> wrap (st := Ing (Refiner.first_unproven t', next, []))
    end
    | Ing (t, t_next::next, prev) ->
      wrap (st:= Ing (Refiner.first_unproven t_next, next, t::prev))

  let prev_branch () = 
    match !st with
    | Idle -> wrap_err "prev_branch fails: there is no working session."
    | Qed _ -> wrap_err "prev_branch fails: there is no unproven subgoal."
    | Ing (t, [], []) -> wrap_err "prev_branch fails: there is only one branch."
    | Ing (t, next, []) -> begin
      match List.rev (t::next) with
      | [] -> assert false
      | t'::prev -> wrap (st := Ing (Refiner.first_unproven t', [], prev))
    end
    | Ing (t, next, t_prev::prev) ->
      wrap (st:= Ing (Refiner.first_unproven t_prev, t::next, prev))
        
  let qed () = 
    match !st with
    | Idle | Ing _ -> assert false
    | Qed t ->
      try
        let lpf = Refiner.proof_of_pftreestate t |! Proof_tree.to_lproof in
        lproof := Some (lpf);
        LCheck.certify lpf |! unwrap "L.certify fails.";
        let cpf = ConvertLC.convert_exn lpf in
        cproof := Some (cpf);
        CCheck.certify cpf |! unwrap "C.certify fails.";
        let spf = ConvertCS.convert_exn cpf in
        sproof := Some (spf);
        SCheck.certify spf |! unwrap "S.certify fails.";
        wrap ()
      with
      | e -> exn_wrap_err ~msg:"qed fails. " e
        
  let step tactic = 
    match !st with
    | Idle -> wrap_err "step fails: there is no working session."
    | Qed _ -> wrap_err "step fails: there is no unproven subgoal."
    | Ing (t, next, prev) ->
      try
        let t' = Refiner.solve_pftreestate (Refiner.refiner tactic) t in
        try 
          wrap (st := Ing (Refiner.first_unproven t', next ,prev))
        with
        | Refiner.Not_found_pf _ -> 
          if Refiner.is_complete_pftreestate t' then
            qed (st := Qed (Refiner.top_of_tree t'))
          else
            next_subgoal (st := Ing (t', next, prev))
      with
      | Failure msg
      | Invalid_argument msg -> wrap_err ("step fails: Not appicable tactic. " ^ msg)
        
  let undo () = 
    match !st with
    | Idle -> wrap_err "undo fails: there is no working session."
    | Qed _ -> wrap_err "undo fails: sorry, but you can not undo a completed proof. Try restart."
    | Ing (t, next, prev) -> 
      let t' = Refiner.traverse 0 t |! Refiner.weak_undo_pftreestate in
      wrap (st := Ing (t', next, prev))

  let auto depth = 
    match !st with
    | Idle -> wrap_err "auto fails: there is no working session."
    | Qed _ -> wrap_err "auto fails: there is no unproven subgoal."
    | Ing (t, next ,prev) ->
      try
        let t' = Search.auto_dfs depth t in
        try 
          wrap (st := Ing (Refiner.first_unproven t', next, prev))
        with
        | Refiner.Not_found_pf _ -> 
          if Refiner.is_complete_pftreestate t' then
            qed (st := Qed (Refiner.top_of_tree t'))
          else
            next_subgoal (st := Ing (t', next, prev))
      with
      | Search.Auto_fail -> wrap_err "auto fails: Cannot find the proof. Try with a deeper depth. ex) auto 3"

  let trivial () = 
    match !st with
    | Idle -> wrap_err "trivial fails: there is no working session."
    | Qed _ -> wrap_err "trivial fails: there is no unproven subgoal."
    | Ing (t, next, prev) ->
      let t' = Search.solve_inv t in
      try 
        wrap (st := Ing (Refiner.first_unproven t', next, prev))
      with
      | Refiner.Not_found_pf _ -> 
        if Refiner.is_complete_pftreestate t' then
          qed (st := Qed (Refiner.top_of_tree t'))
        else
          next_subgoal (st := Ing (t', next, prev))

  let fork () = 
    match !st with
    | Idle -> wrap_err "fork fails: there is no working session."
    | Qed _ -> wrap_err "fork fails: there is no unproven subgoal."
    | Ing (t, next, prev) ->
      wrap (st := Ing (t, (t::next), prev))
        
  let copy_to filename out =
    let f_in = open_in filename in
    try 
      while true do
        (input_line f_in ^ "\n") |! output_string out
      done
    with
    | End_of_file -> close_in f_in

  (* let output_proof to_tex proof tex_name = *)
  (*   let out = open_out tex_name in *)
  (*   let _ = copy_to "tex/prologue.tex" out in *)
  (*   let _ =  *)
  (*     output_string out "\\begin{figure}[!p]\n"; *)
  (*     output_string out "$$\n"; *)
  (*     output_string out (to_tex proof); *)
  (*     output_string out "$$\n"; *)
  (*     output_string out "\\end{figure}\n" in *)
  (*   let _ = copy_to "tex/epilogue.tex" out in *)
  (*   close_out out  *)

  (* let save ~filename = *)
  (*   match !st with *)
  (*   | Idle -> wrap_err "save fails: there is no working session." *)
  (*   | Ing _ -> wrap_err "save fails: proof is not completed." *)
  (*   | Qed _ -> *)
  (*       let lproof = !lproof |! Option.value_exn in *)
  (*       output_proof LWrite.to_tex lproof ("LBBI" ^ filename); *)
  (*       let cproof = !cproof |! Option.value_exn in *)
  (*       output_proof CWrite.to_tex cproof ("CSBBI" ^ filename); *)
  (*       let naive_sproof = !sproof |! Option.value_exn in *)
  (*       output_proof SWrite.to_tex naive_sproof ("NaiveSBBI" ^ filename); *)
  (*       let sproof = CompactS.simplify naive_sproof in *)
  (*       output_proof SWrite.to_tex sproof ("SBBI" ^ filename); *)
  (*       SCheck.certify sproof |! unwrap "S.certify fails"; *)
  (*       wrap () *)

  let output_proof_aux out section to_tex proof =
    output_string out ("\\section{" ^ section ^ "}\n");
    output_string out "\\begin{figure}[here]\n";
    output_string out "$$\n";
    output_string out (to_tex proof);
    output_string out "$$\n";
    output_string out "\\end{figure}\n"

  let save ~filename =
    match !st with
    | Idle -> wrap_err "save fails: there is no working session."
    | Ing _ -> wrap_err "save fails: proof is not completed."
    | Qed _ ->
       let out = open_out filename in
       let _ = copy_to "tex/prologue.tex" out in
       let lproof = !lproof |! Option.value_exn in
       let _ = output_proof_aux out "LBBI proof" LWrite.to_tex lproof in
       let cproof = !cproof |! Option.value_exn in
       let _ = output_proof_aux out "CSBBI proof" CWrite.to_tex cproof in
       let naive_sproof = !sproof |! Option.value_exn in
       let _ = output_proof_aux out "Naive SBBI proof" SWrite.to_tex naive_sproof in
       let sproof = CompactS.simplify naive_sproof in
       let _ = SCheck.certify sproof |! unwrap "S.certify fails" in
       let _ = output_proof_aux out "SBBI proof" SWrite.to_tex sproof in
       let _ = copy_to "tex/epilogue.tex" out in
       close_out out;
       wrap ()

  let save_seq_pic ~filename =
    match !st with
    | Idle -> wrap_err "save_seq fails: there is no working session."
    | Ing _ 
    | Qed _ ->
      try
        let seq = get_goalseq () |! simpl_unwrap in
        let tmp = Filename.temp_file "graph" ".dot" in
        View.ToGraphviz.to_dot_exn ~show_hidden:(!show_hidden_worlds) seq tmp;
        ignore (Sys.command ("dot -Tpng " ^ tmp ^ " -o " ^ filename));
        Sys.remove tmp;
        wrap ()
      with
      | Failure e -> wrap_err ("save_seq_pic fails: " ^ e)

  let show_all () = show_hidden_worlds := true

  let show_visible () = show_hidden_worlds := false

  let show_toggle () = show_hidden_worlds := not !show_hidden_worlds

  let help_msg () =
    Core.Core_string.concat ~sep:"\n"
      ["=================================================================";
       "Simple Interactive Boolean BI prover";
       "";
       "open [Proposition]  : Start a session for a given proposition.";
       "close               : Discard the working session.";
       "restart             : Restart the working session.";
       "apply [Rule] [Args] : Apply a given rule to the goal.";
       "auto /depth/        : Try to solve the focused goal automatically. /depth/ is optional (default 2).";
       "undo                : Cancel the last applied rule.";
       "trivial             : Apply all invertible rules as far as no invertible rule is applicable.";
       (* "next_subgoal        : Focus to the next subgoal."; *)
       (* "prev_subgoal        : Focus to the preivious subgoal."; *)
       "history             : Print the working proof-tree.";
       "save [Filename]     : Save the proof to the file 'Filename'.";
       "help                : Print this message.";
       "quit                : Exit this program.";
       "-----------------------------------------------------------------";
       "";
       "Special Character: T=true F=false I=unit";
       "Variables: [A-EGHJ-SU-Za-z]([A-Za-Z0-9]*)";
       "Connectives(precedence): ->, -*, \\/, /\\, *, !";
       "";
       "Rules and arguments:";
       " Init  [seq index]  [tc index]  [fc index]";
       " TopR  [seq index]  [fc index]";
       " BotL  [seq index]  [tc index]";
       " NegL  [seq index]  [tc index]";
       " NegR  [seq index]  [fc index]";
       " AndL  [seq index]  [tc index]";
       " AndR  [seq index]  [fc index]";
       " OrL   [seq index]  [tc index]";
       " OrR   [seq index]  [fc index]";
       " ImplyL [seq index] [tc index]";
       " ImplyR [seq index] [fc index]";
       " UnitL [seq index]  [tc index]";
       " UnitR [seq index]  [fc index]";
       " StarL [seq index]  [tc index]";
       " StarR [seq index(w)]  [rc index(w1-w2)]  [fc index]";
       " WandL [seq index(w)]  [tc index(wand)]  [seq index(w1)]";
       " WandR [seq index]  [fc index]";
       " Comm  [seq index]  [rc index]";
       " ZeroU [seq index]";
       " ZeroD [seq index(w)]  [seq index(w1)]";
       " Assoc [seq index(w1)]  [seq index(w2)]  [seq index(w3)]";
       "";
       " Arguments of the rules except the rules ZeroD and Assoc";
       " are the same as those of the rules written in the paper.";
       " ex) apply Init 1 1 3 : Apply the rule Init with truth/";
       "     falsehood formulas indexed by 1 and 3, respectively,";
       "     at world indexed by 1.";
       " ";
       " ZeroD [seq index(w)]  [seq index(w1)] := The rule ZeroD ";
       "  requires a world that has a child pair right of which has";
       "  Mzero. The parent world is indexed by [w] and the left";
       "  child is indexed by [w1].";
       " ";
       " Assoc [seq index(w1)]  [seq index(w2)]  [seq index(w3)] := ";
       "  The rule Assoc requires five worlds: w, w', w1, w2, w3.";
       "  The world w has (w', w3) as a child-pair and the world w'";
       "  has (w1, w2) as a child-pair. User has to specify worlds";
       "  w1, w2, and w3 using indexes [w1], [w2], and [w3].";
       "=================================================================";
      ]
end

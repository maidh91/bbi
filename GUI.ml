(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common
open Interactive

(** Setting up UI *)
let window = GWindow.window ~title:"Interactive Prover for Labelled CSBBI" ~border_width:10 ~width:800 ~height:400 () 

let hpaned = GPack.paned `HORIZONTAL ()
  ~packing:window#add;;

(* Left Column *)
let vbox = GPack.vbox ~spacing:5 ~width:315 ~packing:(hpaned#pack1) ()


(* Left Column : State View  & Message View*)
let vpaned = GPack.paned `VERTICAL ()
  ~packing:(vbox#pack ~expand:true);;

let sw_state = GBin.scrolled_window ()
  ~hpolicy:`AUTOMATIC
  ~vpolicy:`AUTOMATIC
  ~packing:(vpaned#pack1);;

let state_view = GText.view ()
  ~editable:false
  ~cursor_visible:false
  ~border_width:2
  ~packing:sw_state#add;;

let sw_message = GBin.scrolled_window ()
  ~hpolicy:`AUTOMATIC
  ~vpolicy:`AUTOMATIC
  ~packing:(vpaned#pack2);;
  
let message_view = GText.view () 
  ~editable:false
  ~cursor_visible:false
  ~border_width:2
  ~packing:sw_message#add;;

(* Left Column : Message View & Entry  *)
let entry = GEdit.entry ()
  ~packing:(vbox#pack ~from:`END);;

(* Right Column *)
let sw_img = GBin.scrolled_window ()
  ~hpolicy:`AUTOMATIC
  ~vpolicy:`AUTOMATIC
  ~packing:(hpaned#pack2 ~resize:true);;

let image = GMisc.image () ~packing:sw_img#add_with_viewport;;

let show_hidden_worlds = ref false

(** Action  *)
let update_state () =
  state_view#buffer#set_text (Session.to_string ());
  match Session.get_goalseq () with
  | Ok seq -> begin
    try
      let tmp = Filename.temp_file "graph" ".png" in
      Session.save_seq_pic tmp |! simpl_unwrap;
      let pixbuf = GdkPixbuf.from_file tmp in
      image#set_pixbuf pixbuf;
      Sys.remove tmp;
    with _ -> ()
  end
  | Error _ -> ();;

let run_command () = 
  try 
    let text = entry#text in
    entry#set_text "";
    let cmd = Command.from_string_exn text in
    try
      begin
        match cmd with
        | Command.Open prop ->
          Session.start_fprop ~fprop:prop
          |! simpl_unwrap
        | Command.Restart ->
          Session.restart ()
          |! simpl_unwrap
        | Command.Close ->
          Session.close ()
          |! simpl_unwrap
        | Command.Apply tac ->
          Session.step tac
          |! simpl_unwrap
        | Command.Undo ->
          Session.undo ()
          |! simpl_unwrap
        | Command.Auto i ->
          Session.auto i
          |! simpl_unwrap
        | Command.Trivial ->
          Session.trivial ()
          |! simpl_unwrap
        | Command.Next_subgoal ->
          Session.next_subgoal ()
          |! simpl_unwrap
        | Command.Prev_subgoal ->
          Session.prev_subgoal ()
          |! simpl_unwrap
        | Command.Next_branch ->
          Session.next_branch ()
          |! simpl_unwrap
        | Command.Prev_branch ->
          Session.prev_branch ()
          |! simpl_unwrap
        | Command.Save filename ->
          Session.save filename
          |! simpl_unwrap
        | Command.Fork ->
          Session.fork ()
          |! simpl_unwrap
        | Command.Print_history ->
          Session.print_history () |! message_view#buffer#set_text
        | Command.Help ->
          Session.help_msg () |! message_view#buffer#set_text
        | Command.Quit ->
          exit 0
        | Command.Save_seq_pic filename ->
          Session.save_seq_pic filename
          |! simpl_unwrap
        | Command.Show_all ->
          Session.show_all ()
        | Command.Show_visible ->
          Session.show_visible ()
        | Command.Show_toggle ->
          Session.show_toggle ()
      end;
      begin
        match cmd with
        | Command.Print_history | Command.Help 
        | Command.Save_seq_pic _ | Command.Save _ -> ()
        | _ -> 
          message_view#buffer#set_text "";
          update_state ()
      end
    with
    | Failure msg -> 
      message_view#buffer#set_text msg
  with Failure msg -> String.concat ["Invalid command"; "\n"; msg] |! message_view#buffer#set_text

(** Initialize  *)
let main () =  
  ignore (window#connect#destroy ~callback:GMain.Main.quit);

  ignore (entry#connect#activate ~callback:run_command);

  window#show ();

  (* This code makes ''entry'' to pose a cursor! *)
  (* GMain.Grab.add entry; *)
  entry#misc#grab_focus ();
  
  GMain.Main.main ()

let _ = main ()

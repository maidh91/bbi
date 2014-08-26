(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Common
open Core.Std
open Interactive

let loop () =
  try begin
      let cmd = Command.from_string_exn (read_line ()) in
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
             |! simpl_unwrap;
             print_endline ("Saved the proof to '" ^ filename ^ "'.")
          | Command.Save_seq_pic filename ->
             Session.save_seq_pic ~filename
             |! simpl_unwrap
          | Command.Fork ->
             Session.fork ()
             |! simpl_unwrap
          | Command.Print_history ->
             Session.print_history () |! print_endline
          | Command.Help ->
             Session.help_msg () |! print_endline
          | Command.Quit ->
             exit 0;
          | Command.Show_all ->
             Session.show_all ()
          | Command.Show_visible ->
             Session.show_visible ()
          | Command.Show_toggle ->
             Session.show_toggle ()
        end;
        print_newline ();
        Session.to_string () |! print_endline
      with
      | Failure msg -> print_endline msg
    end
  with
  | Failure msg ->
     Core.Core_string.concat ~sep:"\n"
                             [ "Invalid command:";
                               msg;]
     |! print_endline
        
let _ =
  try
    Printexc.record_backtrace true;
    Session.init ();
    print_endline  "--------------------------------------------------------------------------------";
    print_endline " Welcome to BBEye prover";
    print_endline "";
    Session.to_string () |! print_endline;
    while true do
      print_endline "--------------------------------------------------------------------------------";
      print_string "> ";
      loop ()
    done
  with
  | (Failure msg) as e ->
    Printexc.print_backtrace stdout |! print_newline;
    print_string msg |! print_newline;
    raise e

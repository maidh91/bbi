(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Core.Std
open Common

type priority = Pri_zero | Pri_one

type local_seq = {
  ew: int;                              (* the number of multZero *)

  rc : (World.t * World.t * priority) list;

  tc_n : Prop.t list;                     (* truth context *)
  tc_r : Prop.t list;
  tc_s : Prop.t list;
  tc_d : Prop.t list;

  fc_n : Prop.t list;                     (* falsehood context *)
  fc_r : Prop.t list;
  fc_s : Prop.t list;
  fc_d : Prop.t list;
}

type seq = {
  all: (World.t * (local_seq * priority)) list;
}

(* TODO: ew, rc, (tc @ tc_r @ tc_d), (fc @ fc_r @ fc_d) *)
let eq_aux (w1, (ls1,_)) (w2, (ls2,_)) = 
  if World.eq w1 w2 then
    try
      eq_list ls1.rc ls2.rc
      |! unwrap "Seq.eq_aux: rc do not agree.";
      eq_list (ls1.tc_n @ ls1.tc_r @ ls1.tc_s) (ls2.tc_n @ ls2.tc_r @ ls2.tc_s)
      |! unwrap "Seq.eq_aux: tc do not agree.";
      eq_list ls1.tc_d ls2.tc_d
      |! unwrap "Seq.eq_aux: tc_d do not agree.";
      eq_list (ls1.fc_n @ ls1.fc_r @ ls1.fc_s) (ls2.fc_n @ ls2.fc_r @ ls2.fc_s)
      |! unwrap "Seq.eq_aux: fc do not agree.";
      eq_list ls1.fc_d ls2.fc_d
      |! unwrap "Seq.eq_aux: fc_d do not agree.";
      if ls1.ew = ls2.ew then wrap ()
      else wrap_err "Seq.eq_aux: ew do not agree" |! simpl_unwrap
    with
    | e -> exn_wrap_err ~msg:"Seq.eq_aux failed." e
  else
    wrap_err "Seq.eq_aux failed. Worlds do not agree"

let eq seq1 seq2 =
  let seq1_s = List.sort ~cmp:(fun (w1,_) (w2,_) -> World.compare w1 w2) seq1.all in
  let seq2_s = List.sort ~cmp:(fun (w1,_) (w2,_) -> World.compare w1 w2) seq2.all in
  let rec eq_rec l1 l2 =
    match l1, l2 with
    | [], [] -> wrap ()
    | a::_, [] -> wrap_err "seq1 is longer"
    | [], b::_ -> wrap_err "seq2 is longer"
    | a::als, b::bls -> 
      eq_aux a b
      |! simpl_unwrap;
      eq_rec als bls
  in
  try eq_rec seq1_s seq2_s
  with e -> exn_wrap_err ~msg:"Seq.eq failed." e

let eq_rc (w1,w2) (wl, wr, p) = World.eq wl w1 && World.eq wr w2
  

let empty_ls = {
  ew=0; rc=[]; 
  tc_n=[]; tc_r=[]; tc_s=[]; tc_d=[]; 
  fc_n=[]; fc_r=[]; fc_s=[]; fc_d=[]} 

(* Converter *)
let of_lseq {LSeq.worlds = wl; LSeq.relations = lrc; LSeq.tcontext = ltc; LSeq.fcontext = lfc} =
  let mk_local_state world =
    let rc = List.rev_filter_map lrc ~f:(fun rel -> 
      if World.eq world rel.LSeq.parent then
        Some (rel.LSeq.lchild, rel.LSeq.rchild, Pri_one)
      else
        None) in
    let tc_pre = List.rev_filter_map ltc ~f:(function
      | (ws, w) when World.eq w world -> Some ws
      | _ -> None) in
    let tc_n = List.rev_filter_map tc_pre ~f:(function
      | LSeq.Prop p -> Some p
      | _ -> None) in
    let ew = List.count tc_pre ~f:(function 
      | LSeq.Mzero -> true
      | _ -> false) in
    let fc_n = List.rev_filter_map lfc ~f:(function
      | (p, w) when World.eq w world -> Some p
      | _ -> None) in
    world, ({ ew; rc;
             tc_n; tc_r = []; tc_d = []; tc_s=[];
             fc_n; fc_r = []; fc_d = []; fc_s=[]}, Pri_one) 
  in
  {
    all = List.map wl ~f:mk_local_state;
  }


let local_state_to_lseq (world, ({ew; rc; 
                                 tc_n; tc_r; tc_s; tc_d; 
                                 fc_n; fc_r; fc_s; fc_d}, _)) =
  let make_lrc (lw, rw, _) = 
    {LSeq.parent=world; LSeq.lchild=lw; LSeq.rchild=rw} in
  let make_ltc_p p = LSeq.Prop p, world in
  let make_lfc p = p, world in
  let lrc = List.map rc ~f:make_lrc in
  let ltc_p = List.map (tc_n @ tc_r @ tc_s) ~f:make_ltc_p in
  let ltc_e = List.init ew ~f:(fun _ -> LSeq.Mzero, world) in
  let lfc = List.map (fc_n @ fc_r @ fc_s) ~f:make_lfc in
  LSeq.create [world] ~rc:lrc ~tc:(ltc_p@ltc_e) ~fc:lfc 
    
let to_lseq {all} = 
  match all with
  | [] -> failwith "to_lseq"
  | lc::lcs ->
    List.fold_left lcs  ~init:(local_state_to_lseq lc)
      ~f:(fun aux ls -> 
        local_state_to_lseq ls 
        |! LSeq.merge aux
        |! simpl_unwrap)

(* All following functions consider all worlds including hidden ones *)
let get_nth_w ls_idx goal =
  List.nth_exn goal.all ls_idx |! fst

let get_nth_rc ls_idx rc_idx goal =
  let _, (ls, _) = List.nth_exn goal.all ls_idx in
  List.nth_exn ls.rc rc_idx

let get_nth_tc ls_idx tc_idx goal =
  let _, (ls, _) = List.nth_exn goal.all ls_idx in
  List.nth_exn (ls.tc_n @ ls.tc_r @ ls.tc_s) tc_idx

let get_nth_fc ls_idx fc_idx goal =
  let _, (ls, _) = List.nth_exn goal.all ls_idx in
  List.nth_exn (ls.fc_n @ ls.fc_r @ ls.fc_s) fc_idx


let find_nth_rc ls_idx f goal =
  let _, (ls, _) = List.nth_exn goal.all ls_idx in
  List.find_exn ls.rc ~f:f

let find_parent (w1, w2) goal =
  List.find_exn goal.all ~f:(fun (_, (ls,_)) -> 
    List.exists ls.rc ~f:(eq_rc (w1,w2))) |! fst

let is_empty w goal =
  let ls,_ = List.Assoc.find_exn goal.all w in
  ls.ew > 0

let is_hidden w goal =
  let _,prio = List.Assoc.find_exn goal.all w in
  prio = Pri_zero

let is_hidden_rel w (w1,w2) seq =
  let ls,_ = List.Assoc.find_exn seq.all w in
  let _,_,p = List.find_exn ls.rc ~f:(eq_rc (w1,w2)) in
  p = Pri_zero
  
let exists_rc w (w1,w2) goal =
  let ls,_ = List.Assoc.find_exn goal.all w in
  List.exists ls.rc ~f:(eq_rc (w1,w2))
  
let exists_tc w prop goal =
  let ls,_ = List.Assoc.find_exn goal.all w in
  List.mem prop ~set:(ls.tc_n @ ls.tc_r @ ls.tc_s)

let exists_fc w prop goal =
  let ls,_ = List.Assoc.find_exn goal.all w in
  List.mem prop ~set:(ls.fc_n @ ls.fc_r @ ls.fc_s)


let find_ls seq w = 
  List.Assoc.find_exn seq.all w |! fst

let list_split_f ~f list = 
  let rec split_aux acc = function
    | [] -> List.rev acc, []
    | a::next ->
      if f a then
        List.rev acc, a::next
      else
        split_aux (a::acc) next
  in
  split_aux [] list

(* [list_split_w w goal] splits a seq list of [goal] into two of which the second list starts with a world [w]. *)

(* val list_split_w : seq -> (World.t * local_seq) list * (World.t * local_seq) list *)
let split_w_all w all =
  list_split_f (fun (w',_) -> World.eq w w') all

let split_w w goal =
  split_w_all w goal.all

let comm_rc w (w1,w2) goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "comm_rc"
  | (_,(ls,ls_p))::goal_tail' -> 
    let rc_hd, rc_tail = list_split_f ls.rc ~f:(eq_rc (w1,w2)) in
    match rc_tail with
    | [] -> failwith "comm_rc"
    | (wl,wr,p)::rc_tail'->
      let new_ls = {ls with rc = rc_hd @ (wr,wl,p)::rc_tail'} in
      {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}


(* TODO: have to delete related relations? *)
let del_w seq w =
  {all = List.Assoc.remove seq.all w }

let del_rc w (w1,w2) goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "del_rc"
  | (_,(ls,ls_p))::goal_tail' -> 
    let rc_hd, rc_tail = list_split_f ls.rc ~f:(eq_rc (w1,w2)) in
    match rc_tail with
    | [] -> failwith "del_rc"
    | _::rc_tail'->
      let new_ls = {ls with rc = rc_hd @ rc_tail'} in
      {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}

let del_tc w prop goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "del_tc"
  | (_,(ls,ls_p))::goal_tail' -> 
    let tc_hd, tc_tail = list_split_f ls.tc_n ~f:((=) prop) in
    match tc_tail with
    | [] -> failwith "del_tc"
    | _::tc_tail'->
      let new_ls = { ls with
        tc_n = tc_hd @ tc_tail'; 
        tc_d = prop::ls.tc_d} in
      {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}

let del_fc w prop goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "del_fc"
  | (_,(ls,ls_p))::goal_tail' -> 
    let fc_hd, fc_tail = list_split_f ((=) prop) ls.fc_n in
    match fc_tail with
    | [] -> failwith "del_fc"
    | _::fc_tail'->
      let new_ls = {ls with
        fc_n = fc_hd @ fc_tail'; 
        fc_d = prop::ls.fc_d} in
      {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}

let mark_tc_r w prop goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "mark_tc_r"
  | (_,(ls,ls_p))::goal_tail' ->
    let tc_hd, tc_tail = list_split_f ((=) prop) ls.tc_n in
    match tc_tail with
    | [] -> failwith "mark_tc_r"
    | _::tc_tail'->
      let new_ls = {ls with 
        tc_n = tc_hd @ tc_tail'; 
        tc_r = prop::ls.tc_r} in
      {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}

let mark_fc_r w prop goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "mark_fc_r"
  | (_,(ls,ls_p))::goal_tail' ->
    let fc_hd, fc_tail = list_split_f ((=) prop) ls.fc_n in
    match fc_tail with
    | [] -> failwith "mark_fc_r"
    | _::fc_tail'->
      let new_ls = {ls with 
        fc_n = fc_hd @ fc_tail'; 
        fc_r = prop::ls.fc_r} in
      {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}

let mark_tc_s w prop goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "mark_tc_s"
  | (_,(ls,ls_p))::goal_tail' ->
    let tc_hd, tc_tail = list_split_f ((=) prop) ls.tc_n in
    match tc_tail with
    | [] -> failwith "mark_tc_s"
    | _::tc_tail'->
      let new_ls = {ls with 
        tc_n = tc_hd @ tc_tail'; 
        tc_s = prop::ls.tc_s} in
      {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}

let mark_fc_s w prop goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "mark_fc_s"
  | (_,(ls,ls_p))::goal_tail' ->
    let fc_hd, fc_tail = list_split_f ((=) prop) ls.fc_n in
    match fc_tail with
    | [] -> failwith "mark_fc_s"
    | _::fc_tail'->
      let new_ls = {ls with 
        fc_n = fc_hd @ fc_tail'; 
        fc_s = prop::ls.fc_s} in
      {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}

let append_ws ws seq = 
  {all = seq.all @ ws}

let cons_w wl seq =
  {all = wl :: seq.all}

let add_rc w wpair_p goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "add_rc"
  | (_,(ls,ls_p))::goal_tail' -> 
    let new_ls = {ls with 
      rc = wpair_p::ls.rc} in
    {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}

let add_tc w prop goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "add_tc"
  | (_,(ls,ls_p))::goal_tail' -> 
    let new_ls = {ls with 
      tc_n = prop::ls.tc_n} in
    {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}

let add_fc w prop goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "add_fc"
  | (_,(ls,ls_p))::goal_tail' -> 
    let new_ls = {ls with 
      fc_n = prop::ls.fc_n} in
    {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}

let add_ew w goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "add_ew"
  | (_,(ls,ls_p))::goal_tail' -> 
    let new_ls = {ls with 
      ew = succ ls.ew} in
    {all = goal_hd @ (w,(new_ls,ls_p)) :: goal_tail'}

let is_atom = function
  | Prop.Atom _ -> true
  | _ -> false

let merge_local_seq ls1 ls2 =
  let ls2_tc_r_n, ls2_tc_r_r = List.partition ls2.tc_r ~f:is_atom in
  let ls2_fc_r_n, ls2_fc_r_r = List.partition ls2.fc_r ~f:is_atom in
  {
    ew = ls1.ew + ls2.ew;
    rc = ls1.rc @ ls2.rc;
    tc_n = ls1.tc_n @ ls2.tc_n @ ls2_tc_r_n;
    tc_r = ls1.tc_r @ ls2_tc_r_r;
    tc_s = ls1.tc_s @ ls2.tc_s;
    tc_d = ls1.tc_d @ ls2.tc_d;
    fc_n = ls1.fc_n @ ls2.fc_n @ ls2_fc_r_n;
    fc_r = ls1.fc_r @ ls2_fc_r_r;
    fc_s = ls1.fc_s @ ls2.fc_s;
    fc_d = ls1.fc_d @ ls2.fc_d;
  }

(* Caution: naive merge. Do not merge any nodes even when they have a same label. *)
let merge_seq seq1 seq2 = 
  {all = seq1.all @ seq2.all;}

let make_rename ?(rule=(fun _ -> World.get_fresh ())) seq =
  List.split seq.all |! fst |! List.map ~f:(fun w -> w, rule w) |! Map.of_alist_exn

let apply_rename_aux rename (w, (ls,ls_p)) = 
  let rc = List.map ls.rc ~f:(fun (w1,w2,p) -> 
    World.rename_exn rename w1, World.rename_exn rename w2, p) in
  World.rename_exn rename w, ({ls with rc}, ls_p)
    
let apply_rename rename seq = 
  {all = List.map seq.all ~f:(apply_rename_aux rename);}

let hide_ls_rc all w =
  let all_hd, all_tail = split_w_all w all in
  match all_tail with
  | [] -> failwith "hide_all_rc"
  | (_,(ls,_))::all_tail' -> 
    let rc = List.map ls.rc ~f:(fun (w1,w2,_) -> (w1,w2,Pri_zero)) in
    all_hd @ (w, ({ls with rc},Pri_zero)) :: all_tail'

let hide_ws ws {all;} = 
  {all = List.fold_left ws ~init:all ~f:hide_ls_rc;}

let hide_rc w (w1,w2) goal =
  let goal_hd, goal_tail = split_w w goal in
  match goal_tail with
  | [] -> failwith "hide_rc"
  | (_,(ls,ls_p))::goal_tail' -> 
    let rc_hd, rc_tail = list_split_f ls.rc ~f:(eq_rc (w1,w2)) in
    match rc_tail with
    | [] -> failwith "hide_rc"
    | _::rc_tail'->
      let ls = {ls with rc = rc_hd @ (w1,w2,Pri_zero) :: rc_tail'} in
      {all = goal_hd @ (w,(ls,ls_p)) :: goal_tail'}

(* let reveal_ws ws seq = *)
(*   {seq with hidden = List.fold_left ws ~init:seq.hidden ~f:Set.remove} *)

let visible_worlds {all} = 
  List.filter_map all ~f:(function 
  | (w,(_,Pri_one)) -> Some w
  | _ -> None)

let hidden_worlds {all} = 
  List.filter_map all ~f:(function 
  | (w,(_,Pri_zero)) -> Some w
  | _ -> None)
  
let all_worlds seq = 
  List.split seq.all |! fst
      
(* Pretty printer *)
(* let local_seq_to_string_dgb lc = *)
(*   let ew = "isEmpty= " ^ (if lc.ew = 0 then "False" else "True") in *)
(*   let rc = List.foldi lc.rc ~init:"rc=" ~f:(fun i aux (lw,rw,_) ->  *)
(*     aux ^ " " ^ string_of_int i ^ ":" ^ World.to_string lw ^ "-" ^ World.to_string rw) in *)
(*   let tc = List.foldi lc.tc ~init:"tc=" ~f:(fun i aux p ->  *)
(*     aux ^ " " ^ string_of_int i ^ ":" ^ Prop.Writer.to_string p) in *)
(*   let tc_r = List.foldi lc.tc_r ~init:"tc_r=" ~f:(fun i aux p ->  *)
(*     aux ^ " " ^ string_of_int i ^ ":" ^ Prop.Writer.to_string p) in *)
(*   let tc_d = List.foldi lc.tc_d ~init:"tc_d=" ~f:(fun i aux p ->  *)
(*     aux ^ " " ^ string_of_int i ^ ":" ^ Prop.Writer.to_string p) in *)
(*   let fc = List.foldi lc.fc ~init:"fc=" ~f:(fun i aux p ->  *)
(*     aux ^ " " ^ string_of_int i ^ ":" ^ Prop.Writer.to_string p) in *)
(*   let fc_r = List.foldi lc.fc_r ~init:"fc_r=" ~f:(fun i aux p ->  *)
(*     aux ^ " " ^ string_of_int i ^ ":" ^ Prop.Writer.to_string p) in *)
(*   let fc_d = List.foldi lc.fc_d ~init:"fc_d=" ~f:(fun i aux p ->  *)
(*     aux ^ " " ^ string_of_int i ^ ":" ^ Prop.Writer.to_string p) in *)
(*   ew ^ "\n" ^ rc ^ "\n" ^  *)
(*     tc ^ "\n" ^ tc_r ^ "\n" ^ tc_d ^ "\n" ^ *)
(*     fc ^ "\n" ^ fc_r ^ "\n" ^ fc_d ^ "\n" *)

let get_ls_idx goal w = 
  List.findi goal.all ~f:(fun i (w',_) -> World.eq w w')
  |! Option.value_exn |! fst

let get_rc_idx goal ls_idx (w1,w2) =
  let ls,_ = List.nth_exn goal.all ls_idx |! snd in
  List.findi ls.rc ~f:(fun i rel -> eq_rc (w1,w2) rel)
  |! Option.value_exn |! fst

let get_tc_idx goal ls_idx prop =
  let ls,_ = List.nth_exn goal.all ls_idx |! snd in
  List.findi (ls.tc_n @ ls.tc_r @ ls.tc_s) ~f:(fun i prop' -> prop = prop')
  |! Option.value_exn |! fst

let get_fc_idx goal ls_idx prop =
  let ls,_ = List.nth_exn goal.all ls_idx |! snd in
  List.findi (ls.fc_n @ ls.fc_r @ ls.fc_s) ~f:(fun i prop' -> prop = prop')
  |! Option.value_exn |! fst


let local_seq_to_string show_hidden seq lc =
  let ew = if lc.ew = 0 then "" else " <MZero>\n" in
  let rc = List.foldi lc.rc ~init:"" ~f:(fun i aux (lw,rw,rc_p) -> 
    if show_hidden || rc_p = Pri_one then 
      aux ^ " " ^ string_of_int i ^ ":" ^ World.to_string lw ^ "-" ^ World.to_string rw
    else
      aux) in
  let tc = List.foldi (lc.tc_n @ lc.tc_r @ lc.tc_s)  ~init:"" ~f:(fun i aux p -> 
    aux ^ " " ^ string_of_int i ^ ":" ^ Prop.Writer.to_string p) in
  let fc = List.foldi (lc.fc_n @ lc.fc_r @ lc.fc_s) ~init:"" ~f:(fun i aux p -> 
    aux ^ " " ^ string_of_int i ^ ":" ^ Prop.Writer.to_string p) in
  let rc = if rc = "" then rc else "  GS="^rc^"\n" in
  let tc = if tc = "" then tc else "  TC="^tc^"\n" in
  let fc = if fc = "" then fc else "  FC="^fc^"\n" in
  ew ^ rc ^ tc ^ fc

let to_string ?(show_hidden=false) seq =
  List.foldi seq.all ~init:"" ~f:(fun i aux (w,(ls,ls_p)) ->
    if show_hidden || ls_p = Pri_one then
      aux ^ "\n" ^
        "Seq #" ^ string_of_int i ^ ": " ^ World.to_string w ^ "\n" ^
        local_seq_to_string show_hidden seq ls
    else
      aux)

(* This file is distributed under the terms of the GNU Lesser General Public License Version 2.1 *)
(* Jeongbong Seo, Jonghyun Park, Sungwoo Park *)
(* Programming Language Laboratory, POSTECH *)
(* {baramseo, parjong, gla}@postech.ac.kr *)

open Common
open Core.Std
(* open Format *)

module ToGraphviz :
sig
  val to_dot_exn : Seq.seq -> ?show_hidden:bool -> string -> unit
end
=
struct

  type vtype = 
  | World of (int list * int * bool)               (* world idx * is_hidden *)
  | Relation of int list * int * int * Seq.priority

  type etype = LCHILD | RCHILD | PARENT | TRANS

  module V =
  struct
    type t = vtype
    let compare v1 v2 =
      match v1, v2 with
      | World _, Relation _ -> -1
      | Relation (_, w1,r1,_), Relation (_, w2,r2,_) ->
          if w1 = w2 then
              r1 - r2
          else
              w1 - w2
      | World (_, w1, _), World (_, w2, _) -> w1 - w2
      | Relation _, World _ -> 1
    let hash = Hashtbl.hash
    let equal v1 v2 = 
      match v1, v2 with
      | World _, Relation _ 
      | Relation _, World _ -> false
      | Relation (_, w1,r1,_), Relation (_, w2,r2,_) -> (w1 = w2) && (r1 = r2)
      | World (_, w1, _), World (_, w2, _) -> (w1 = w2)
  end
    
  module E =
  struct
    type t = etype
    let compare a b = 
      match a, b with
      | LCHILD, RCHILD -> -1
      | LCHILD, PARENT -> -1
      | PARENT, RCHILD -> -1
      | PARENT, LCHILD -> 1
      | RCHILD, LCHILD -> 1
      | RCHILD, PARENT -> 1
      | _ -> 0
    let default = PARENT
  end
    
  module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(V)(E)

  let seq = ref ([])
  let g = G.create ()
  let g' = G.create ()
  let g'' = G.create ()
    
  let escape_lt str =
    Core.Core_string.split str ~on:'\\'
    |! Core.Core_string.concat ~sep:"\\\\"
    |! Core.Core_string.split ~on:'>'
    |! Core.Core_string.concat ~sep:"\\>"
        
  let tc_to_string i prop =
    Printf.sprintf "t%-2d: %s" i (Prop.Writer.to_string prop |! escape_lt)
      
  let fc_to_string i prop =
    Printf.sprintf "f%-2d: %s" i (Prop.Writer.to_string prop |! escape_lt)

  open Gviz.DotAttributes

  module Display = struct
    include G
    let vertex_name v = 
      match V.label v with
      | World (_, i,_) -> "w" ^ string_of_int i
      | Relation (_, w, r, _) -> "w" ^ string_of_int w ^ "g" ^ string_of_int r
    let graph_attributes _ = 
      [`Fontsize 9;
       `Fontname "arial";
       `Margin 0.1; ]
    let default_vertex_attributes _ = 
      [`Fontsize 9;
       `Fontname "monospace";]
    let get_world_label i =
      let w, (w_ls,w_ls_p) = List.nth_exn !seq i in
      let empty = if w_ls.Seq.ew > 0 then "\\<MZero\\>\\n" else "" in
      let tctx = List.mapi (w_ls.Seq.tc_n @ w_ls.Seq.tc_r @ w_ls.Seq.tc_s) ~f:tc_to_string in
      let fctx = List.mapi (w_ls.Seq.fc_n @ w_ls.Seq.fc_r @ w_ls.Seq.fc_s) ~f:fc_to_string in
      "{Seq #" ^ string_of_int i ^ ": " ^ World.to_string w
      ^ "|" ^ empty ^ Core.Core_string.concat ~sep:"\\n" tctx 
      ^ "|" ^ Core.Core_string.concat ~sep:"\\n" fctx  
      ^ "}" 
    let vertex_attributes v =
      match V.label v with
      | World (_, i, hidden) -> 
        if hidden then
          [`Shape `Record; `Label (get_world_label i)] 
        else
          [`Shape `Record; `Label (get_world_label i); `Color 0x00AA00] 
      | Relation (_, w,r,_) -> [`Label ("g" ^ string_of_int r)]
      (* | Relation (_, w,r,Seq.Pri_zero) -> [`Label ("r" ^ string_of_int r ^ "(0)")] *)
      (* | Relation (_, w,r,Seq.Pri_one) -> [`Label ("r" ^ string_of_int r ^ "(1)")] *)
    let default_edge_attributes _ = [`Fontsize 9; ]
    let edge_attributes e = 
      match E.label e with
      | PARENT -> []
      | TRANS -> [`Color 0xFFFFFF; `Weight 2]
      | LCHILD -> [`Color 0xee0000; `Fontcolor 0xee0000; `Label "L"; `Style `Bold]
      | RCHILD -> [`Color 0x80; `Fontcolor 0x80; `Label "R"; `Style `Solid]
    let get_subgraph _ = None

    let get_vertex_list t = 
        let cmp_cluster v1 v2 =
            (match v1, v2 with
            | World (t1, _,_), Relation (t2, _,_,_) 
            | Relation (t1, _,_,_), World (t2, _,_)
            | Relation (t1, _,_,_), Relation (t2, _,_,_)
            | World (t1, _, _), World (t2, _, _) -> List.compare (List.rev t1) (List.rev t2) (fun a b -> a - b))
        in
            List.sort cmp_cluster (G.fold_vertex (fun v l -> v::l) t [])
    let get_sg_name v =
        match V.label v with
            World (tl, _, _) -> List.rev tl
        |   Relation (tl, _, _, _) -> List.rev tl
  end

  module Dot_ = Gviz.Dot(Display)

  let to_dot_exn s ?(show_hidden=false) f =
    let _ = seq := s.Seq.all in
    let _ = G.clear g in
    let world_vertex_map = List.filter_mapi s.Seq.all ~f:(fun i (w,_) -> 
      if show_hidden || not (Seq.is_hidden w s) then 
        Some (w, (i, G.V.create (World ([], i, (Seq.is_hidden w s)))))
      else
        None) in
    let _ = List.iter world_vertex_map ~f:(fun (_,(_,v)) -> G.add_vertex g v) in
    let _ = List.iter s.Seq.all ~f:(fun (w, (ls,ls_p)) ->
      match List.Assoc.find world_vertex_map w with
      | None -> ()
      | Some (wi, p) ->
        List.iteri ls.Seq.rc ~f:(fun ri (wl, wr, pri) ->
          if show_hidden || (not (Seq.is_hidden wl s) && not (Seq.is_hidden wr s)) then
            let v = G.V.create (Relation ([], wi, ri, pri)) in
            let _, lc = List.Assoc.find_exn world_vertex_map wl in
            let _, rc = List.Assoc.find_exn world_vertex_map wr in
            let lc_e = G.E.create v LCHILD lc in
            let rc_e = G.E.create v RCHILD rc in
            G.add_vertex g v;
            G.add_edge g p v;
            G.add_edge_e g lc_e;
            G.add_edge_e g rc_e))
    in
    let _ = G.clear g' in
    let _ = G.clear g'' in
    let source = G.fold_vertex (fun v1 v2 -> 
        match v1, v2 with
        |   World (_, i1, _), World (_, i2, _) -> if i1 <= i2 then v1 else v2
        |   _ -> v2) g (World ([], 1073741823, true))
    in
    let add_vtag i v =
        match v with
        | World (tl, wi, b) -> (World (i::tl, wi, b))
        | Relation (tl, wi, ri, p) -> Relation (i::tl, wi, ri, p)
    in
    let get_vtag v =
        match v with
        | World (tl, _, _) -> tl
        | Relation (tl, _, _, _) -> tl
    in
    let inherit_vtag l v =
        match v with
        | World (tl, wi, b) -> (World (l, wi, b))
        | Relation (tl, wi, ri, p) -> Relation (l, wi, ri, p)
    in
    let remove_vtag v =
        match v with
        | World (tl, wi, b) -> (World ([], wi, b))
        | Relation (tl, wi, ri, p) -> Relation ([], wi, ri, p)
    in
    let top_vertex g v = 
      let diff ed ve = 
        match G.E.label ed, G.V.label ve with
        | PARENT, World _ -> 1
        | PARENT, Relation _ -> -1
        | _, World _ -> -1
        | _, Relation _ -> 1
      in
      let rec top_vertex' i v = 
        let sucl = G.succ g v in
        match sucl with
        | [] -> (i, v)
        | _ -> 
           begin
             let list = List.map sucl (fun sv-> let edge = (G.find_edge g v sv) in
                                                top_vertex' (i + diff edge sv) sv) in
             List.fold_right list ~f:(fun va vb -> 
                                      if fst va >= fst vb then va 
                                      else vb) ~init:(i, v)
           (* let tovn = match v with World (_, n, _) -> n | Relation (_, n, m,_) -> n*1000 + m in *)
           (* let topvtxn = match b with World (_, n, _) -> n | Relation (_, n, m,_) -> n*1000 + m in *)
           (* open_box 0;  *)
           (* print_string ("call of : ");  *)
           (* print_int i;  *)
           (* print_string ("     to world: ");  *)
           (* print_int tovn;  *)
           (* print_string ("     top world is : ");  *)
           (* print_int topvtxn;  *)
           (* close_box ();  *)
           (* print_newline ();  *)
           end
      in 
      (* let tovn = match v with World (_, n, _) -> n | Relation (_, n, m,_) -> n*1000 + m in *)
      (* print_newline (); *)
      (* open_box 0;  *)
      (* print_string ("initial call of : 0 ");  *)
      (* print_string ("     to world: ");  *)
      (* print_int tovn;  *)
      (* close_box ();  *)
      (* print_newline ();  *)
      (top_vertex' 0 v)
    in
    (*
    *)
    let rec clustering g s =
        let sgene = get_vtag s in
        let plist = List.mapi (List.map (G.pred g (remove_vtag s)) (inherit_vtag sgene)) add_vtag in
        let pn = List.length plist in
        let clist = List.mapi (List.map (G.succ g (remove_vtag s)) (inherit_vtag sgene)) (fun n v -> add_vtag (pn + n) v) in
        
        if List.length (plist @ clist) = 0 then () 
        else (
        let (eplist, eplist') = List.split (List.map plist (fun v -> 
            let edge = G.E.label (G.find_edge g (remove_vtag v) (remove_vtag s)) 
            in (G.E.create v edge s, G.E.create s edge v))) 
        in
        let (eclist, eclist') = List.split (List.map clist (fun v -> 
            G.E.create s PARENT v, G.E.create s PARENT v)) 
        in
        let _ = 
            List.iter eplist (fun edge -> G.add_edge_e g' edge);
            List.iter eclist (fun edge -> G.add_edge_e g' edge);
            List.iter eplist' (fun edge -> G.add_edge_e g'' edge);
            List.iter eclist' (fun edge -> G.add_edge_e g'' edge);
            G.remove_vertex g (remove_vtag s)
        in
        let pworlds = List.mapi
            ( List.fold_right 
                ( List.map plist 
                    ~f:(fun v -> let gene = get_vtag v in
                        (List.map ((G.pred g (remove_vtag v))@(G.succ g (remove_vtag v))) 
                            ~f:(fun v' -> (v, inherit_vtag gene v'))))) 
                ~f:(fun a b -> a @ b) ~init:[])
            ~f:(fun i (r, w) -> (r, add_vtag i w))
        in
        let pwn = List.length pworlds in
        let cworlds = List.mapi (
            List.fold_right (
                List.map clist ~f:(fun v -> 
                    let gene = get_vtag v in
                    (List.map ((G.succ g (remove_vtag v))) ~f:(fun v' -> (v, inherit_vtag gene v')))
                )
            ) 
            ~f:(fun a b -> 
            a @ b) ~init:[]
            ) ~f:(fun i (r, w) -> 
            (r, add_vtag (pwn + i) w))
        in

        let (epworld, epworld') = List.split (List.map pworlds (fun (r, w) -> 
            begin try let (_, edge, _) = (G.find_edge g (remove_vtag r) (remove_vtag w)) in (G.E.create r edge w, G.E.create r edge w)
            with Not_found -> (G.E.create w PARENT r, G.E.create r PARENT w) end ))
        in
        let (ecworld, ecworld') = List.split (List.map cworlds (fun (r, w) -> 
            let (_, edge, _) = (G.find_edge g (remove_vtag r) (remove_vtag w)) 
            in (G.E.create r edge w, G.E.create r edge w)))
        in
        let _ = 
            List.iter epworld (fun edge -> G.add_edge_e g' edge);
            List.iter ecworld (fun edge -> G.add_edge_e g' edge);
            List.iter epworld' (fun edge -> G.add_edge_e g'' edge);
            List.iter ecworld' (fun edge -> G.add_edge_e g'' edge);
            List.iter plist (fun v -> G.remove_vertex g (remove_vtag v));
            List.iter clist (fun v -> G.remove_vertex g (remove_vtag v))
        in
        List.iter (pworlds @ cworlds) (fun (_, w) -> clustering g w)
        )
    in
    let vsource = G.V.create source in
    let vsource' = G.V.create source in
    let _ = G.add_vertex g' vsource; G.add_vertex g'' vsource'; clustering g source in
    let rec successive_v_iter f g v = f v;G.iter_succ (successive_v_iter f g) g v in
    (*
    let _ = G.iter_vertex  
    *)
    let _ = successive_v_iter  
        (fun v -> match G.succ g' v with 
            |   _::_ -> ()
            |   [] -> let (r, topv) = top_vertex g'' v in
                if topv = v || List.exists ~f:(fun e -> match G.E.label e with TRANS -> true | _ -> false) (G.pred_e g' topv) then ()
                else match (G.pred g'' v) with
                    |   [] -> ()
                    |   x::_ -> let tr_edge = G.E.create x TRANS topv 
                        in G.add_edge_e g' tr_edge) g'' source
    in
    let oc = open_out f in
    Dot_.output_graph oc g' g'';
    close_out oc
end

(* let _ = ToGraphviz.to_dot_exn (Sexp.load_sexp "lseq.txt" |! LSeq.t_of_sexp) "test.dot" *)

(* let display_with_gv seq = *)
(*   let tmp = Filename.temp_file "graph" ".dot" in *)
(*   ToGraphviz.to_dot_exn seq tmp; *)
(*   ignore (Sys.command ("dot -Tps " ^ tmp ^ " | gv -")); *)
(*   Sys.remove tmp *)

(*
let _ = display_with_gv (Sexp.load_sexp "lseq.txt" |! LSeq.t_of_sexp)
 *)

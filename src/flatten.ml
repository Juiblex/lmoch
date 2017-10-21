(* flatten the node so that we only have idents and consts
 * inside of pre and -> *)


open Util
open Typed_ast
open Asttypes
open Ident

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

let rec makevars name = function
  | 0 -> []
  | k -> (Ident.make (name ^ (string_of_int k)) Stream)::(makevars name (k-1))

(* Same as inline: we return a list of variables, their stream equations, and
 * the new expression *)
let rec flatten_expr e = match e.texpr_desc with
  | TE_const _ -> [], [], e
  | TE_ident _ -> [], [], e
  | TE_op (o, exprs) ->
      let vars, streams, exprs' = 
        match o with
(*        | Op_if -> split3 (List.map (create_auxs "ite_aux") exprs) *)
          | _ -> split3 (List.map flatten_expr exprs) in
      List.concat vars, List.concat streams,
        {e with texpr_desc = TE_op (o, exprs')}
  | TE_app (_, _) -> failwith "there shouldn't be node applications"
  | TE_prim (prim, exprs) ->
      let vars, streams, exprs' = split3 (List.map flatten_expr exprs) in
      List.concat vars, List.concat streams,
        {e with texpr_desc = TE_prim (prim, exprs')}
  | TE_arrow (e1, e2) ->
(*    let v1, s1, e1' = create_auxs "arr_aux" e1 in
      let v2, s2, e2' = create_auxs "arr_aux" e2 in *)
      let v1, s1, e1' = flatten_expr e1 in
      let v2, s2, e2' = flatten_expr e2 in
      v1 @ v2, s1 @ s2, {e with texpr_desc = TE_arrow (e1', e2')}
  | TE_pre e1 -> 
      let vars, streams, e' = create_auxs "pre_aux" e1 in
      vars, streams, {e with texpr_desc = TE_pre e'}
  | TE_tuple exprs ->
      let vars, streams, exprs' = split3 (List.map flatten_expr exprs) in
      List.concat vars, List.concat streams, {e with texpr_desc = TE_tuple exprs'}

and create_auxs name e = match e.texpr_desc with
    | TE_ident _ -> [], [], e
    | TE_const _ -> [], [], e
    | _ -> (* new equation : (aux1, ..., auxn)  = e *)
        let vars, streams, e = flatten_expr e in
        let typ = e.texpr_type in
        let auxs = makevars name (List.length typ) in
        let equ = { teq_patt = { tpatt_desc = auxs; tpatt_type = typ;
                                 tpatt_loc = dummy_loc };
                    teq_expr = e } in
        let typed_auxs = List.combine auxs typ in
        let make_id (id, typ) = 
          { texpr_desc = TE_ident id;
            texpr_type = [typ];
            texpr_loc = Lexing.dummy_pos, Lexing.dummy_pos } in
        let tuple = { texpr_desc = TE_tuple (List.map make_id typed_auxs);
                      texpr_type = typ;
                      texpr_loc = dummy_loc } in
        typed_auxs@vars, equ::streams, tuple

let flatten_equ equ =
  let vars, streams, e' = flatten_expr equ.teq_expr in
  vars, streams, {equ with teq_expr = e'}

let flatten_node node =
  let vars, streams, equs = split3 (List.map flatten_equ node.tn_equs) in
  { node with tn_local = (List.concat vars)@node.tn_local;
              tn_equs = (List.concat streams)@equs }

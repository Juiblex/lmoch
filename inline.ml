open Typed_ast
open Ident
open Asttypes
open Util

(* gives fresh names to the variables in the node *)
let rename node =
  let rec rename_e var nvar e = 
    let desc = match e.texpr_desc with
    | TE_const _ -> e.texpr_desc
    | TE_ident id -> TE_ident (if id = var then nvar else id)
    | TE_op (o, exprs) -> TE_op (o, List.map (rename_e var nvar) exprs)
    | TE_app (id, args) -> TE_app (id, List.map (rename_e var nvar) args)
    | TE_prim (id, args) -> TE_prim (id, List.map (rename_e var nvar) args)
    | TE_pre e -> TE_pre (rename_e var nvar e)
    | TE_arrow (e1, e2) -> TE_arrow (rename_e var nvar e1, rename_e var nvar e2)
    | TE_tuple exprs -> TE_tuple (List.map (rename_e var nvar) exprs)
    in {e with texpr_desc = desc}
  in

  let rename_patt var nvar patt =
    {patt with tpatt_desc =
      List.map (fun id -> if id = var then nvar else id) patt.tpatt_desc} in

  let rename_eq var nvar {teq_patt = patt; teq_expr = expr} =
    {teq_patt = rename_patt var nvar patt; teq_expr = rename_e var nvar expr} in

  let rename_loc node var =
    let nvar = Ident.make (var.name ^ "_" ^ node.tn_name.name) Stream in
    let loc =
      List.map (fun (id, t) -> if id = var then nvar, t else id, t) node.tn_local in
    let equs = List.map (rename_eq var nvar) node.tn_equs in
    {node with tn_local = loc; tn_equs = equs} in

  let rename_out node var = 
    let nvar = Ident.make (var.name ^ "_" ^ node.tn_name.name) Stream in
    let out =
      List.map (fun (id, t) -> if id = var then nvar, t else id, t) node.tn_output in
    let equs = List.map (rename_eq var nvar) node.tn_equs in
    {node with tn_output = out; tn_equs = equs} in

  let rename_in node var = 
    let nvar = Ident.make (var.name ^ "_" ^ node.tn_name.name) Stream in
    let out =
      List.map (fun (id, t) -> if id = var then nvar, t else id, t) node.tn_input in
    let equs = List.map (rename_eq var nvar) node.tn_equs in
    {node with tn_input = out; tn_equs = equs} in

  let node = List.fold_left
    (fun node (id, t) -> rename_loc node id) node node.tn_local in
  let node = List.fold_left
    (fun node (id, t) -> rename_out node id) node node.tn_output in
  let node = List.fold_left
    (fun node (id, t) -> rename_in node id) node node.tn_input in
  node

(* Returns a list of new local variables, a list of equations describing the
 * new streams and their definitions and a new expression in which the calls
 * to nodes are replaced by the new streams *)
let rec inline_expr p e = match e.texpr_desc with
  | TE_const _ -> [], [], e
  | TE_ident _ -> [], [], e
  | TE_op (o, exprs) ->
      let vars, streams, exprs' = split3 (List.map (inline_expr p) exprs) in
      List.concat vars, List.concat streams, {e with texpr_desc = TE_op (o, exprs')}
  | TE_app (id, args) ->
      let node = List.find (fun n -> n.tn_name = id) p in
      let node = rename node in
      let node = inline_node p node in
      let assign_input_equ =
        { teq_patt = { tpatt_desc = List.map fst node.tn_input;
                       tpatt_type = List.map snd node.tn_input;
                       tpatt_loc = Lexing.dummy_pos, Lexing.dummy_pos };
          teq_expr = { texpr_desc = TE_tuple args;
                       texpr_type = List.map snd node.tn_input;
                       texpr_loc = Lexing.dummy_pos, Lexing.dummy_pos } } in
      let make_id (id, typ) = 
        { texpr_desc = TE_ident id;
          texpr_type = [typ];
          texpr_loc = Lexing.dummy_pos, Lexing.dummy_pos } in
      let out_tuple = TE_tuple (List.map make_id node.tn_output) in
      node.tn_input@node.tn_local@node.tn_output,
        (assign_input_equ::node.tn_equs), {e with texpr_desc = out_tuple}
      
  | TE_prim (id, args) ->
      let vars, streams, args' = split3 (List.map (inline_expr p) args) in
      List.concat vars, List.concat streams, {e with texpr_desc = TE_prim (id, args')}
  | TE_arrow (e1, e2) ->
      let v1, s1, e1' = inline_expr p e1 in
      let v2, s2, e2' = inline_expr p e2 in
      v1 @ v2, s1 @ s2, {e with texpr_desc = TE_arrow (e1', e2')}
  | TE_pre e ->
      let v, s, e' = inline_expr p e in
      v, s, {e with texpr_desc = TE_pre e'}
  | TE_tuple exprs ->
      let vars, streams, exprs' = split3 (List.map (inline_expr p) exprs) in
      List.concat vars, List.concat streams, {e with texpr_desc = TE_tuple exprs'}

and inline_equ p eq =
  let vars, streams, e' = inline_expr p eq.teq_expr in
  vars, streams, {eq with teq_expr = e'}

and inline_node p node =
  let vars, streams, equs = split3 (List.map (inline_equ p) node.tn_equs) in
  { node with tn_local = (List.concat vars) @ node.tn_local;
              tn_equs = (List.concat streams) @ equs } 

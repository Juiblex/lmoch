(* Takes a Lustre node with one boolean output, and runs k-induction on it
 * to try proving that the output is always true *)

open Asttypes
open Typed_ast
open Ident
open Util

open Z3

type result =
  | Proved
  | Disproved
  | Failed

let (funsymbs: (Ident.t, Z3.FuncDecl.func_decl) Hashtbl.t) = Hashtbl.create 17

let cfg = [("model", "true"); ("proof", "true")]
let ctx = mk_context cfg
let type_bool = Z3.Boolean.mk_sort ctx
let type_int = Z3.Arithmetic.Integer.mk_sort ctx
let type_real = Z3.Arithmetic.Real.mk_sort ctx

let dec_fun name t_in t_out =
  let x = Z3.Symbol.mk_string ctx name in
  Z3.FuncDecl.mk_func_decl ctx x t_in t_out

let ttype = function
  | Tbool -> type_bool
  | Tint -> type_int
  | Treal -> type_real

let tconst = function
  | Cbool b -> if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx
  | Cint n -> Z3.Arithmetic.Integer.mk_numeral_i ctx n
  | Creal x -> failwith "reals not supported"

let zero = tconst (Cint 0)
let one = tconst (Cint 1)
let ttrue = tconst (Cbool true)
let tfalse = tconst (Cbool false)

(* [translate_expr n e] turns [e] into a list of terms applied at time [n] *)
(* [n] has type Term.t *)
let rec translate_expr n e = match e.texpr_desc with
  | TE_const c -> [tconst c]
  | TE_ident id ->
      let symb = Hashtbl.find funsymbs id in
      [Z3.Expr.mk_app ctx symb [n]]
  | TE_op (op, exprs) ->
      (* all these are expected not to be tuples *)
      let texprs = List.map (translate_expr n) exprs in
      let texprs = List.map List.hd texprs in
      let term = match op with
        | Op_eq -> let [t1; t2] = texprs in
            Z3.Boolean.mk_eq ctx t1 t2
        | Op_neq ->
            Z3.Boolean.mk_distinct ctx texprs (* check that *)
        | Op_le -> let [t1; t2] = texprs in
            Z3.Arithmetic.mk_le ctx t1 t2
        | Op_lt -> let [t1; t2] = texprs in
            Z3.Arithmetic.mk_lt ctx t1 t2
        | Op_ge -> let [t1; t2] = texprs in
            Z3.Arithmetic.mk_ge ctx t1 t2
        | Op_gt -> let [t1; t2] = texprs in
            Z3.Arithmetic.mk_gt ctx t1 t2
        | Op_add | Op_add_f ->
            Z3.Arithmetic.mk_add ctx texprs
        | Op_sub | Op_sub_f ->
            Z3.Arithmetic.mk_sub ctx texprs
        | Op_mul | Op_mul_f ->
            Z3.Arithmetic.mk_mul ctx texprs
        | Op_div | Op_div_f -> let [t1; t2] = texprs in
            Z3.Arithmetic.mk_div ctx t1 t2
        | Op_mod -> let [t1; t2] = texprs in
            Z3.FloatingPoint.mk_rem ctx t1 t2
        | Op_not ->
            Z3.Boolean.mk_not ctx (List.hd texprs)
        | Op_and ->
            Z3.Boolean.mk_and ctx texprs
        | Op_or ->
            Z3.Boolean.mk_or ctx texprs
        | Op_impl -> let [t1; t2] = texprs in
            Z3.Boolean.mk_implies ctx t1 t2
        | Op_if -> let [t1; t2; t3] = texprs in
            Z3.Boolean.mk_ite ctx t1 t2 t3
      in [term]
  | TE_app (_, _) -> failwith "no more applications"
  | TE_prim (_, _) -> failwith "TODO"
  | TE_arrow (e1, e2) ->
      let te1 = translate_expr n e1 in
      let te2 = translate_expr n e2 in
      List.map2 (Z3.Boolean.mk_ite ctx (Z3.Boolean.mk_eq ctx n zero)) te1 te2
  | TE_pre e ->
      translate_expr (Z3.Arithmetic.mk_sub ctx [n; one]) e
  | TE_tuple exprs ->
      let texprs = List.map (translate_expr n) exprs in
      List.concat texprs

let translate_equ n equ =
  let terms = translate_expr n equ.teq_expr in
  let make_formula id t =
    Z3.Boolean.mk_eq ctx
      (Z3.Expr.mk_app ctx (Hashtbl.find funsymbs id) [n]) t in
  let formulas = List.map2 make_formula equ.teq_patt.tpatt_desc terms in
  Z3.Boolean.mk_and ctx formulas

let delta node n =
  let formulas = List.map (translate_equ n) node.tn_equs in
  Z3.Boolean.mk_and ctx formulas

let n_t = Z3.Expr.mk_app ctx (dec_fun "@n" [] type_int) []

let print_f f = Format.printf "%s\n@." (Z3.Expr.to_string f)

let base_case delta p k =
  let rec make_n prop = function
    | 0 -> [prop zero]
    | k -> (prop (tconst (Cint k)))::(make_n prop (k-1)) in
  let hyps = Z3.Boolean.mk_and ctx (make_n delta k) in
  let goal = Z3.Boolean.mk_and ctx (make_n p k) in
  let solver = Z3.Solver.mk_simple_solver ctx in
  Format.printf "Trying %d-induction base case.@." k;
  Z3.Solver.add solver [hyps];
  Z3.Solver.add solver [Z3.Boolean.mk_not ctx goal];
  Z3.Solver.check solver [] = Z3.Solver.UNSATISFIABLE

let ind_case delta p c k =
  let rec make_n prop = function
    | 0 -> [prop n_t]
    | k -> let n_k = Z3.Arithmetic.mk_add ctx [n_t; tconst (Cint k)] in
        (prop n_k)::(make_n prop (k-1)) in

  let hyps = Z3.Boolean.mk_and ctx ((make_n delta (k+1))@(make_n p k)) in
  let add_hyps = c n_t k in
  let n_k_1 = Z3.Arithmetic.mk_add ctx [n_t; tconst (Cint k); one] in
  let goal = p n_k_1 in
  Format.printf "Trying %d-induction inductive case.@." k;
  let solver = Z3.Solver.mk_simple_solver ctx in
  Z3.Solver.add solver [hyps];  
  Z3.Solver.add solver [add_hyps];
(*List.iter print_f (Z3.Solver.get_assertions solver); *)
  Z3.Solver.add solver [Z3.Boolean.mk_not ctx goal];
  Z3.Solver.check solver [] = Z3.Solver.UNSATISFIABLE

let induction delta p c k =
  if base_case delta p k = false then Disproved
  else if ind_case delta p c k = true then Proved
  else Failed 

let state_vars_n node =
  let rec state_vars_expr e = match e.texpr_desc with
    | TE_const _ | TE_ident _ -> []
    | TE_op (_, es) -> List.flatten (List.map state_vars_expr es)
    | TE_app (_, _) | TE_prim (_, _) -> failwith "no apps"
    | TE_arrow (e1, e2) -> (state_vars_expr e1) @ (state_vars_expr e2)
    | TE_pre e' -> begin match e'.texpr_desc with
      | TE_ident i -> [i]
      | _ -> failwith "flattening failed"
      end
    | TE_tuple es -> List.flatten (List.map state_vars_expr es)
  in
  let state_vars_eq eq = state_vars_expr eq.teq_expr in
  List.flatten (List.map state_vars_eq node.tn_equs)

let solve node kmax =
  List.iter (fun (id, typ) -> Hashtbl.add funsymbs id
    (dec_fun (Ident.string_of id) [type_int] (ttype typ)))
    (node.tn_input @ node.tn_local @ node.tn_output);

(*  Hashtbl.iter (fun id _ -> Printf.printf "%s__%d " id.name id.id) funsymbs;  *)

  let delta_incr n = delta node n in

  let p_incr n =
    let out, _ = List.hd node.tn_output in
    let ok = Hashtbl.find funsymbs out in
    Z3.Boolean.mk_eq ctx (Z3.Expr.mk_app ctx ok [n]) ttrue in

  let state_vars = state_vars_n node in

  (* formula expressing that the states at times i and j are different *)
  (* i and j are terms  *)
  let distinct_state i j =
    let equal_v i j id =
      let v = Hashtbl.find funsymbs id in
      Z3.Boolean.mk_eq ctx
        (Z3.Expr.mk_app ctx v [i])
        (Z3.Expr.mk_app ctx v [j]) in
    let res =
    Z3.Boolean.mk_not ctx
      (Z3.Boolean.mk_and ctx (List.map (equal_v i j) state_vars)) in
    Format.printf "states at %s and %s are different:@."
      (Z3.Expr.to_string i) (Z3.Expr.to_string j);
   (* print_f res;*)
    res in

  (* formula expressing that all the states for j < i+l are different from *
   * the state at i+l *)
  (* i is a term and l an integer *)
  let distinct_end i l =
    let end_t = Z3.Arithmetic.mk_add ctx [i; tconst (Cint l)] in
    let rec dist_k k = match k with
      | 0 -> [distinct_state i end_t]
      | _ -> let i_k = Z3.Arithmetic.mk_add ctx [i; tconst (Cint k)] in
          (distinct_state i_k end_t)::(dist_k (k-1)) in
    Z3.Boolean.mk_and ctx (dist_k (l-1)) in

  (* formula expressing that the path is compressed between n and n+k *)
  (* k is an integer but n is a term *)
  let compressed n k =
    let rec interm_j j = 
      let rec interm_i i = match i with
        | 0 -> [distinct_end n j]
        | _ -> let n_i = Z3.Arithmetic.mk_add ctx [n; tconst (Cint i)] in
            (distinct_end n_i (j-i))::(interm_i (i-1)) in
      let n_j = Z3.Arithmetic.mk_add ctx [n; tconst (Cint j)] in
      Z3.Boolean.mk_and ctx ((distinct_state zero n_j)::(interm_i (j-1))) in
    let rec conjs = function
      | 0 -> [delta_incr zero]
      | j -> (interm_j j)::(conjs (j-1)) in
    let res = Z3.Boolean.mk_and ctx (conjs k) in
(*    print_f res;*)
    res in

  
(*  let _n = Z3.Expr.mk_app ctx (dec_fun "n" [] type_int) [] in
  let delta = delta_incr _n in
  let p = p_incr _n in
  Format.printf "Delta: %s\nGoal: %s@."
    (Z3.Expr.to_string delta) (Z3.Expr.to_string p);
*)
  let rec try_ind k =
    if k > kmax then Failed
    else begin
      Format.printf "Trying %d-induction.@." k;
      match induction delta_incr p_incr compressed k with
        | Proved -> Proved
        | Disproved -> Disproved
        | Failed -> try_ind (k+1)
    end
  in try_ind 0

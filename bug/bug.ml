(* Takes a Lustre node with one boolean output, and runs k-induction on it
 * to try proving that the output is always true *)

open Asttypes
open Typed_ast
open Ident

open Z3

type result =
  | Proved
  | Disproved
  | Failed

let (symbs: (Ident.t, Z3.Symbol.symbol) Hashtbl.t) = Hashtbl.create 17

let ctx = mk_context []
let type_bool = Z3.Boolean.mk_sort ctx
let type_int = Z3.Arithmetic.Integer.mk_sort ctx
let type_real = Z3.Arithmetic.Real.mk_sort ctx

let dec_fun name t_in t_out =
  let x = Z3.Symbol.mk_string name in
  Z3.FuncDecl.mk_func_decl x t_in t_out

let dec_aux name =
  let auxid = Ident.make name Stream in
  dec_fun (auxid.name ^ (string_of_int auxid.id)) [Type.type_int] Type.type_bool

let ttype = function
  | Tbool -> type_bool
  | Tint -> type_int
  | Treal -> type_real

let tconst = function
  | Cbool b -> if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx
  | Cint n -> Z3.Arithmetic.Integer.mk_numeral_i ctx n
  | Creal x -> (*Term.make_real (Num.?? x) *) failwith "reals not supported"

let ftoterm f =
  Term.make_ite f Term.t_true Term.t_false
  
let termtrue t = Formula.make_lit Formula.Eq [t; Term.t_true]
let termfalse t = Formula.make_lit Formula.Eq [t; Term.t_false]

let equiv f1 f2 = Formula.make Formula.And
  [Formula.make Formula.Imp [f1; f2]; Formula.make Formula.Imp [f2; f1]]

let zero = tconst (Cint 0)
let one = tconst (Cint 1)

(* Having a Formula.And with a list of size 1 crashes the solver *)
let make_ands = function
  | [] -> Formula.f_true
  | [f] -> f
  | l -> Formula.make Formula.And l

(* [translate_expr n e] turns [e] into a list of terms applied at time [n],
 * and a list of auxiliary formulas (for ands, nots...) *)
(* [n] has type Term.t *)
(*
let rec translate_expr n e = match e.texpr_desc with
  | TE_const c -> [tconst c], []
  | TE_ident id ->
      let symb = Hashtbl.find symbs id in
      [Term.make_app symb [n]], []
  | TE_op (op, exprs) ->
      (* all these are expected not to be tuples *)
      let texprs, fs = List.split (List.map (translate_expr n) exprs) in
      let texprs = List.map List.hd texprs in
      let term, newfs =
      begin match op with
        | Op_eq ->
            ftoterm (Formula.make_lit Formula.Eq texprs), []
        | Op_neq ->
            ftoterm (Formula.make_lit Formula.Neq texprs), []
        | Op_le ->
            ftoterm (Formula.make_lit Formula.Le texprs), []
        | Op_lt ->
            ftoterm (Formula.make_lit Formula.Lt texprs), []
        | Op_ge ->
            ftoterm (Formula.make_lit Formula.Le (List.rev texprs)), []
        | Op_gt ->
            ftoterm (Formula.make_lit Formula.Lt (List.rev texprs)), []
        | Op_add | Op_add_f -> let [t1; t2] = texprs in
            Term.make_arith Term.Plus t1 t2, []
        | Op_sub | Op_sub_f -> let [t1; t2] = texprs in
            Term.make_arith Term.Minus t1 t2, []
        | Op_mul | Op_mul_f -> let [t1; t2] = texprs in
            Term.make_arith Term.Mult t1 t2, []
        | Op_div | Op_div_f -> let [t1; t2] = texprs in
            Term.make_arith Term.Div t1 t2, []
        | Op_mod -> let [t1; t2] = texprs in
            Term.make_arith Term.Modulo t1 t2, []
        | Op_not ->
            let term = List.hd texprs in
            let aux = dec_aux "@auxnot" in (* it's a symbol *)
            let auxn = Term.make_app aux [n] in auxn,
              [equiv (termtrue term) (termtrue auxn)]
        | Op_and ->
            let andforms = Formula.make Formula.And
              (List.map termtrue texprs) in
            let aux = dec_aux "@auxand" in
            let auxn = Term.make_app aux [n] in
            auxn, [equiv andforms (termtrue auxn)]
        | Op_or ->
            let orforms = Formula.make Formula.Or
              (List.map termtrue texprs) in
            let aux = dec_aux "@auxor" in
            let auxn = Term.make_app aux [n] in
            auxn, [equiv orforms (termtrue auxn)]
        | Op_impl ->
            let impforms = Formula.make Formula.Imp
              (List.map termtrue texprs) in
            let aux = dec_aux "@auximp" in
            let auxn = Term.make_app aux [n] in
            auxn, [equiv impforms (termtrue auxn)]
        | Op_if -> let [t1; t2; t3] = texprs in
            let aux = dec_aux "@auxif" in
            let auxn = Term.make_app aux [n] in
            let impt = Formula.make Formula.Imp
              [termtrue t1; equiv (termtrue auxn) (termtrue t2)] in
            let impf = Formula.make Formula.Imp
              [termfalse t1; equiv (termtrue auxn) (termtrue t3)] in
            auxn, [impt; impf]
      end in
      [term], newfs @ (List.concat fs)
  | TE_app (_, _) -> failwith "no more applications"
  | TE_prim (_, _) -> failwith "TODO"
  | TE_arrow (e1, e2) ->
      let te1, f1 = translate_expr n e1 in
      let te2, f2 = translate_expr n e2 in
      List.map2 (Term.make_ite (Formula.make_lit Formula.Eq [n; zero])) te1 te2,
        f1 @ f2
  | TE_pre e ->
      translate_expr (Term.make_arith Term.Minus n one) e
  | TE_tuple exprs ->
      let texprs, fs = List.split (List.map (translate_expr n) exprs) in
      List.concat texprs, List.concat fs

let translate_equ n equ =
  let terms, fs = translate_expr n equ.teq_expr in
  let make_formula id t =
    Formula.make_lit Formula.Eq [Term.make_app (Hashtbl.find symbs id) [n]; t] in
  let formulas = List.map2 make_formula equ.teq_patt.tpatt_desc terms in
  make_ands (formulas @ fs)

let delta node n =
  let formulas = List.map (translate_equ n) node.tn_equs in
  make_ands formulas

*)

let n_t = Term.make_app (dec_fun "@n" [] Type.type_int) []
let k_t = Term.make_app (dec_fun "@k" [] Type.type_int) []
let n_k_1 = Term.make_arith Term.Plus (Term.make_arith Term.Plus n_t k_t) one

let base_case delta p k =
  let rec add_hyps = function
    | -1 -> ()
    | k -> (*Formula.print Format.std_formatter (delta (Term.make_int (Num.Int k)));
          print_newline (); *)
        BMC_solver.assume ~id:0 (delta (Term.make_int (Num.Int k)));
           add_hyps (k-1) in
  let rec make_goal = function
    | 0 -> [p zero]
    | k -> (p (Term.make_int (Num.Int k)))::(make_goal (k-1)) in
  let goal = make_ands (make_goal k) in
  BMC_solver.clear ();
  add_hyps k;
  BMC_solver.check ();
(*  Formula.print Format.std_formatter goal;
  print_newline ();*)
  Format.printf "Trying %d-induction base case.@." k;
  BMC_solver.entails ~id:0 goal

let ind_case delta p k =
  let rec add_hyps = function
    | 0 -> IND_solver.assume ~id:0 (delta n_k_1);
    | m ->
        let n_k_1_m = Term.make_arith Term.Minus n_k_1 (Term.make_int (Num.Int m)) in
        IND_solver.assume ~id:0 (delta n_k_1_m);
        IND_solver.assume ~id:0 (p n_k_1_m);
        add_hyps (m-1) in
  let goal = p n_k_1 in
  IND_solver.clear ();
  add_hyps (k+1);
  IND_solver.check ();
  Format.printf "Trying %d-induction inductive case.@." k;
  IND_solver.entails ~id:0 goal

let induction delta p k =
  if base_case delta p k = false then Disproved
  else if ind_case delta p k = true then Proved
  else Failed 

let solve node kmax =
  List.iter (fun (id, typ) -> Hashtbl.add symbs id
    (dec_fun (Ident.string_of id) [type_int] (ttype typ)))
    (node.tn_input @ node.tn_local @ node.tn_output);

(*  Hashtbl.iter (fun id _ -> Printf.printf "%s__%d " id.name id.id) symbs;  *)

  let delta_incr n = delta node n in

  let p_incr n =
    let out, _ = List.hd node.tn_output in
    let ok = Hashtbl.find symbs out in
    Formula.make_lit Formula.Eq [Term.make_app ok [n]; Term.t_true] in

  let n = Expr.mk_app ctx (dec_fun "n" [] Type.type_int) [] in
  Formula.print Format.std_formatter (delta_incr n);
  print_string "\n";
  Formula.print Format.std_formatter (p_incr n);
  print_string "\n";

  let rec try_ind k =
    if k > kmax then Failed
    else begin
      Format.printf "trying %d\n@." k;
      match induction delta_incr p_incr k with
        | Proved -> Proved
        | Disproved -> Disproved
        | Failed -> try_ind (k+1)
    end
  in try_ind 0

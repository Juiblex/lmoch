(* Takes a Lustre node with one boolean output, and runs k-induction on it
 * to try proving that the output is always true *)

open Asttypes
open Typed_ast
open Ident

open Aez
open Smt

module Imap = Map.Make(Ident)

module BMC_Solver = Smt.Make(struct end)
module IND_Solver = Smt.Make(struct end)

type result =
  | Proved
  | Disproved
  | Failed

type terms =
  | Tbase of Term.t
  | Ttuple of terms list

let dec_symb name t_in t_out =
  let x = Hstring.make name in
  Symbol.declare x t_in t_out;
  x

let ttype = function
  | Tbool -> Type.type_bool
  | Tint -> Type.type_int
  | Treal -> Type.type_real

let tconst = function
  | Cbool b -> if b then Term.t_true else Term.t_false
  | Cint n -> Term.make_int (Num.num_of_int n)
  | Creal x -> (*Term.make_real (Num.?? x) *) failwith "reals not supported"

let ftoterm f =
  Term.make_ite f Term.t_true Term.t_false

let termtof t =
  Formula.make_lit Formula.Eq [t; Term.t_true] 

let zero = Term.make_int (Num.Int 0)
let one = Term.make_int (Num.Int 1)

(* [translate_expr n e] turns [e] into a terms applied at time [n] *)
(* [n] has type Term.t *)
let rec translate_expr symbs n e = match e.texpr_desc with
  | TE_const c -> Tbase (tconst c)
  | TE_ident id ->
      let symb = Imap.find id symbs in
      Tbase (Term.make_app symb [n])
  | TE_op (op, exprs) ->
      (* all these are expected not to be tuples *)
      let texprs = List.map (translate_expr symbs n) exprs in
      let texprs = List.map (fun (Tbase t) -> t) texprs in
      let term =
      begin match op with
        | Op_eq ->
            ftoterm (Formula.make_lit Formula.Eq texprs)
        | Op_neq ->
            ftoterm (Formula.make_lit Formula.Neq texprs)
        | Op_le ->
            ftoterm (Formula.make_lit Formula.Le texprs)
        | Op_lt ->
            ftoterm (Formula.make_lit Formula.Lt texprs)
        | Op_ge ->
            ftoterm (Formula.make_lit Formula.Le (List.rev texprs))
        | Op_gt ->
            ftoterm (Formula.make_lit Formula.Lt (List.rev texprs))
        | Op_add | Op_add_f -> let [t1; t2] = texprs in
            Term.make_arith Term.Plus t1 t2
        | Op_sub | Op_sub_f -> let [t1; t2] = texprs in
            Term.make_arith Term.Minus t1 t2
        | Op_mul | Op_mul_f -> let [t1; t2] = texprs in
            Term.make_arith Term.Mult t1 t2
        | Op_div | Op_div_f -> let [t1; t2] = texprs in
            Term.make_arith Term.Div t1 t2
        | Op_mod -> let [t1; t2] = texprs in
            Term.make_arith Term.Modulo t1 t2
        | Op_not ->
            ftoterm (Formula.make Formula.Not (List.map termtof texprs))
        | Op_and ->
            ftoterm (Formula.make Formula.And (List.map termtof texprs))
        | Op_or ->
            ftoterm (Formula.make Formula.Or (List.map termtof texprs))
        | Op_impl ->
            ftoterm (Formula.make Formula.Imp (List.map termtof texprs))
        | Op_if -> let [t1; t2; t3] = texprs in
            Term.make_ite (termtof t1) t2 t2
      end in
      Tbase term
  | TE_app (_, _) -> failwith "no more applications"
  | TE_prim (_, _) -> failwith "TODO"
  | TE_arrow (e1, e2) ->
      let te1 = translate_expr symbs n e1 in
      let te2 = translate_expr symbs n e2 in
      let rec transl = function
        | Tbase t1, Tbase t2 ->
            Tbase (Term.make_ite (Formula.make_lit Formula.Eq [n; zero]) t1 t2)
        | Ttuple ts1, Ttuple ts2 ->
            Ttuple (List.map transl (List.combine ts1 ts2))
      in transl (te1, te2)
  | TE_pre e ->
      translate_expr symbs
        (Term.make_arith Term.Minus n one) e
  | TE_tuple exprs ->
      Ttuple (List.map (translate_expr symbs n) exprs)

let rec flatten = function (* turns a terms into a term list *)
  | Tbase t -> [t]
  | Ttuple l -> List.concat (List.map flatten l)

let translate_equ symbs n equ =
  let terms = flatten (translate_expr symbs n equ.teq_expr) in
  let make_formula id t =
    Formula.make_lit Formula.Eq [Term.make_app (Imap.find id symbs) [n]; t] in
  let formulas = List.map2 make_formula equ.teq_patt.tpatt_desc terms in
  Formula.make Formula.And formulas

let delta symbs n node =
  let formulas = List.map (translate_equ symbs n) node.tn_equs in
  Formula.make Formula.And formulas

let solve node =
  let symbs = List.fold_left
    (fun map (id, typ) -> Imap.add id (dec_symb (id.name ^ (string_of_int id.id))
      [Type.type_int] (ttype typ)) map)
    Imap.empty (node.tn_input @ node.tn_local @ node.tn_output) in

  let n = Term.make_app (dec_symb "n" [] Type.type_int) [] in
  let delta_n = delta symbs n node in
  Formula.print Format.std_formatter delta_n;
  Failed

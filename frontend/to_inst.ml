open Ast
open To_id
open Ocaml5_parser
open Mtyped
open Zzdatatype.Datatype
open Parsetree
open To_constant

let rec inst_of_expr expr =
  match expr.pexp_desc with
  | Pexp_ident id -> IVar (longid_to_id id) #: None
  | Pexp_constant _ | Pexp_array _ -> IConst (expr_to_constant expr)
  | Pexp_apply (func, args) ->
      let func = inst_of_expr func in
      let args = List.map (fun x -> inst_of_expr @@ snd x) args in
      List.fold_left (fun res arg -> IApp (res, arg)) func args
  | Pexp_let (_, [ v ], body) ->
      let lhs = (id_of_pattern v.pvb_pat) #: None in
      let rhs = inst_of_expr v.pvb_expr in
      ILet { lhs; rhs; body = inst_of_expr body }
  | _ -> IQregex (To_qregex.of_expr (To_regex.of_expr To_sevent.of_expr) expr)

let layout_inst layout_t expr =
  let rec aux expr =
    match expr with
    | IConst c -> layout_constant c
    | IApp (op, arg) -> spf "%s %s" (aux op) (aux arg)
    | IAtomicF { args; regex } ->
        List.fold_right
          (fun arg res -> spf "fun %s -> %s" arg.x res)
          args
          (To_regex.layout To_sevent.layout regex)
    | ILet { lhs; rhs; body } ->
        spf "let %s = %s in %s" lhs.x (aux rhs) (aux body)
    | IQregex q ->
        spf "(%s)"
        @@ To_qregex.layout layout_t (To_regex.layout To_sevent.layout) q
    | IVar x -> x.x
  in
  aux expr

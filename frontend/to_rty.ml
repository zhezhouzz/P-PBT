open Zutils
open OcamlParser
open Parsetree
open Zdatatype
open Ast
open AutomataLibrary

let layout_cty { nt; phi } = spf "v:%s | %s" (Nt.layout nt) (layout_prop phi)

let vars_phi_of_expr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint (e', ct) ->
        let v = get_self ct in
        let vs, phi = aux e' in
        (v :: vs, phi)
    | _ -> ([], prop_of_expr expr)
  in
  let vs, prop = aux expr in
  (List.rev vs, prop)

let cty_of_expr expr =
  match vars_phi_of_expr expr with
  | [ { x; ty } ], phi when String.equal x default_v -> { nt = ty; phi }
  | _ -> _die_with [%here] (Pprintast.string_of_expression expr)

let rec layout_haft = function
  | RtyBase cty -> spf "{%s}" (layout_cty cty)
  | RtyHAF { history; adding; future } ->
      spf "[%s][%s][%s]"
        (layout_symbolic_regex history)
        (layout_symbolic_regex adding)
        (layout_symbolic_regex future)
  | RtyArr { arg; argcty; retrty } ->
      spf "(%s:{%s}) → %s" arg (layout_cty argcty) (layout_haft retrty)
  | RtyInter (haft1, haft2) ->
      spf "%s ⊓ %s" (layout_haft haft1) (layout_haft haft2)

let rec haft_of_expr expr =
  match expr.pexp_desc with
  | Pexp_constraint _ -> RtyBase (cty_of_expr expr)
  | Pexp_fun (_, haftexpr, pattern, body) -> (
      let retrty = haft_of_expr body in
      match haftexpr with
      | None -> _die_with [%here] "wrong format"
      | Some haftexpr ->
          let arg = id_of_pattern pattern in
          let argcty = cty_of_expr haftexpr in
          RtyArr { argcty; arg; retrty })
  | Pexp_let (_, [ vb ], body) ->
      let retrty = haft_of_expr body in
      let arg = id_of_pattern vb.pvb_pat in
      let argcty = cty_of_expr vb.pvb_expr in
      RtyArr { argcty; arg; retrty }
  | Pexp_tuple [ h; a; f ] ->
      let history, adding, future = map3 symbolic_regex_of_expr (h, a, f) in
      RtyHAF { history; adding; future }
  | Pexp_array ls -> mk_inter_type @@ List.map haft_of_expr ls
  | _ ->
      _die_with [%here]
        (spf "wrong refinement type: %s" (Pprintast.string_of_expression expr))

let rec locally_rename_haft ctx = function
  | RtyBase cty -> RtyBase cty
  | RtyHAF { history; adding; future } ->
      let history, adding, future =
        map3 (locally_rename (ctx_to_list ctx)) (history, adding, future)
      in
      RtyHAF { history; adding; future }
  | RtyArr { arg; argcty; retrty } ->
      RtyArr { arg; argcty; retrty = locally_rename_haft ctx retrty }
  | RtyInter (haft1, haft2) ->
      RtyInter (locally_rename_haft ctx haft1, locally_rename_haft ctx haft2)

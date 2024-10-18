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

let rec layout_haft f = function
  | RtyBase cty ->
      if is_true cty.phi then Nt.layout cty.nt else spf "{%s}" (layout_cty cty)
  | RtyHAF { history; adding; future } ->
      spf "[%s][%s][%s]" (f history) (f adding) (f future)
  | RtyHAParallel { history; adding_se; parallel } ->
      spf "[%s][%s][| %s |]" (f history) (layout_se adding_se)
        (List.split_by " " layout_se parallel)
  | RtyArr { arg; argcty; retrty } ->
      let str =
        if is_true argcty.phi then Nt.layout argcty.nt
        else spf "{%s}" (layout_cty argcty)
      in
      spf "(%s:%s) → %s" arg str (layout_haft f retrty)
  | RtyGArr { arg; argnt; retrty } ->
      spf "(%s:%s) ⇢ %s" arg (Nt.layout argnt) (layout_haft f retrty)
  | RtyInter (haft1, haft2) ->
      spf "%s ⊓ %s" (layout_haft f haft1) (layout_haft f haft2)

let rec haft_of_expr expr =
  match expr.pexp_desc with
  | Pexp_constraint _ -> RtyBase (cty_of_expr expr)
  | Pexp_fun (_, haftexpr, pattern, body) -> (
      let retrty = haft_of_expr body in
      match haftexpr with
      | None ->
          let x =
            match pattern.ppat_desc with
            | Ppat_constraint (name, ct) ->
                (id_of_pattern name) #: (Nt.core_type_to_t ct)
            | _ -> _die_with [%here] "wrong format"
          in
          RtyGArr { argnt = x.ty; arg = x.x; retrty }
      | Some haftexpr ->
          let arg = id_of_pattern pattern in
          let argcty = cty_of_expr haftexpr in
          RtyArr { argcty; arg; retrty })
  | Pexp_let (_, [ vb ], body) ->
      let retrty = haft_of_expr body in
      let arg = id_of_pattern vb.pvb_pat in
      let argcty = cty_of_expr vb.pvb_expr in
      RtyArr { argcty; arg; retrty }
  | Pexp_tuple [ h; a; f ] -> (
      match f.pexp_desc with
      | Pexp_array es ->
          let history = symbolic_regex_of_expr h in
          let adding_se = sevent_of_expr a in
          let parallel = List.map sevent_of_expr es in
          RtyHAParallel { history; adding_se; parallel }
      | _ ->
          let history, adding = map2 symbolic_regex_of_expr (h, a) in
          let future = symbolic_regex_of_expr f in
          RtyHAF { history; adding; future })
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
  | RtyHAParallel { history; adding_se; parallel } ->
      let history = (locally_rename (ctx_to_list ctx)) history in
      let adding_se = (locally_rename_se (ctx_to_list ctx)) adding_se in
      let parallel = List.map (locally_rename_se (ctx_to_list ctx)) parallel in
      RtyHAParallel { history; adding_se; parallel }
  | RtyArr { arg; argcty; retrty } ->
      RtyArr { arg; argcty; retrty = locally_rename_haft ctx retrty }
  | RtyGArr { arg; argnt; retrty } ->
      RtyGArr { arg; argnt; retrty = locally_rename_haft ctx retrty }
  | RtyInter (haft1, haft2) ->
      RtyInter (locally_rename_haft ctx haft1, locally_rename_haft ctx haft2)

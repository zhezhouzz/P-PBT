open Ast
open Ocaml5_parser
open Parsetree

let of_expr regex_of_expr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_fun (_, _, arg, expr) -> (
        let open To_notation in
        let q, qv = notation_of_expr arg in
        let body = aux expr in
        match q with
        | FA -> RForall { qv; body }
        | EX -> RExists { qv; body }
        | PI -> RPi { sort = qv; body })
    | _ -> Regex (regex_of_expr expr)
  in
  aux expr

let layout layout_ty layout_regex e =
  let rec aux = function
    | Regex regex -> layout_regex regex
    | RForall { qv; body } ->
        spf "∀(%s:%s).%s" qv.x (layout_ty qv.ty) (aux body)
    | RExists { qv; body } ->
        spf "∃(%s:%s).%s" qv.x (layout_ty qv.ty) (aux body)
    | RPi { sort; body } ->
        spf "Π(%s<:%s).%s" sort.x (layout_ty sort.ty) (aux body)
  in
  aux e

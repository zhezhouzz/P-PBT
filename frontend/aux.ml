open Ocaml5_parser
open Mutils
open Mtyped
open Parsetree
module Nt = Normalty.Frontend

let mk_app_expr func args =
  let args = List.map (fun x -> (Asttypes.Nolabel, x)) args in
  desc_to_ocamlexpr @@ Pexp_apply (func, args)

let mk_tuple_expr es = desc_to_ocamlexpr @@ Pexp_tuple es

let typed_to_expr f expr =
  match expr.ty with
  | None -> f expr.x
  | Some ty ->
      desc_to_ocamlexpr @@ Pexp_constraint (f expr.x, Nt.t_to_core_type ty)

let update_ty { x; ty } ty' =
  match ty with None -> x #: (Some ty') | Some _ -> x #: (Some ty')

let notated (name, t) =
  desc_to_ct
  @@ Ptyp_extension (Location.mknoloc name, PTyp (Nt.t_to_core_type t))

let quantifier_to_pattern (q, u) =
  dest_to_pat
    (Ppat_constraint
       ( dest_to_pat (Ppat_var (Location.mknoloc u.x)),
         notated (Normalty.Connective.qt_to_string q, u.ty) ))

open Sugar

let smt_layout_ty = function
  | Some Nt.T.Ty_bool -> "Bool"
  | Some Nt.T.Ty_int -> "Int"
  | Some (Nt.T.Ty_constructor _) -> "Int"
  | _ -> _failatwith __FILE__ __LINE__ "unimp"

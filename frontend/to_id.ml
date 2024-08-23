open Ocaml5_parser
open Parsetree
open Sugar
open Mutils
open Mtyped
module Nt = Normalty.Frontend
(* open Syntax.NTyped *)

let opt_typed_id_to_pattern id =
  let pat = string_to_pattern id.x in
  match id.ty with
  | None -> pat
  | Some ty -> typed_to_pattern (pat, Nt.t_to_core_type ty)

let opt_typed_ids_to_pattern ids =
  tuple_to_pattern (List.map opt_typed_id_to_pattern ids)

let longid_to_id c =
  match Longident.flatten c.Location.txt with
  | [] -> _die [%here]
  | [ c ] -> c
  | _ -> _failatwith __FILE__ __LINE__ "un-imp"

let id_to_longid x =
  match Longident.unflatten [ x ] with
  | Some x -> Location.mknoloc x
  | None -> _die [%here]

let id_of_pattern pattern =
  match pattern.ppat_desc with
  | Ppat_var ident -> ident.txt
  | Ppat_any -> "_"
  | Ppat_construct (name, None) -> longid_to_id name
  | _ -> _die [%here]

let id_of_expr expr =
  match expr.pexp_desc with
  | Pexp_ident id -> longid_to_id id
  | _ ->
      Pprintast.expression Format.std_formatter expr;
      failwith "die"

let id_of_expr_opt expr =
  match expr.pexp_desc with
  | Pexp_ident id -> Some (longid_to_id id)
  | _ -> None

let rec typed_id_of_expr expr =
  match expr.pexp_desc with
  | Pexp_constraint (expr, ty) ->
      (typed_id_of_expr expr).x #: (Some (Nt.core_type_to_t ty))
  | Pexp_ident id -> (longid_to_id id) #: None
  | _ ->
      Pprintast.expression Format.std_formatter expr;
      failwith "die"

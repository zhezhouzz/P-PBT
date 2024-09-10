open Ast

let rec constant_to_nt c =
  let open Nt in
  match c with
  | U -> Ty_unit
  | B _ -> Ty_bool
  | I _ -> Ty_int
  | Tu l -> Nt.Ty_tuple (List.map constant_to_nt l)
  | Dt _ | SetLiteral _ -> failwith "Not implemented"

(* let compare_constant e1 e2 = *)
(*   Sexplib.Sexp.compare (sexp_of_constant e1) (sexp_of_constant e2) *)

(* let equal_constant e1 e2 = *)
(*   Sexplib.Sexp.equal (sexp_of_constant e1) (sexp_of_constant e2) *)
(* (\* Generated from _constant.ml *\) *)

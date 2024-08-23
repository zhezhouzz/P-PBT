open Syntax
open P_expr_typing
open Zzdatatype.Datatype

type t = Nt.t

let func_check (ctx : t ctx) ({ params; local_vars; body } : t option p_func)
    (ty : t) : (t, t p_func) typed =
  let params = List.map (__force_typed __FILE__ __LINE__) params in
  let local_vars = List.map (__force_typed __FILE__ __LINE__) local_vars in
  let ctx = add_to_rights ctx params in
  let ctx = add_to_rights ctx local_vars in
  let body = typed_expr_check ctx body ty in
  let fty = Nt.construct_arr_tp (List.map _get_ty params, body.ty) in
  { params; local_vars; body } #: fty

let func_infer (ctx : t ctx) ({ params; local_vars; body } : t option p_func) :
    (t, t p_func) typed =
  let params = List.map (__force_typed __FILE__ __LINE__) params in
  let local_vars = List.map (__force_typed __FILE__ __LINE__) local_vars in
  let ctx = add_to_rights ctx params in
  let ctx = add_to_rights ctx local_vars in
  (* let () = *)
  (*   Printf.printf "ctx: %s\n" @@ List.split_by_comma _get_x @@ ctx_to_list ctx *)
  (* in *)
  (* let () = Printf.printf "body: %s\n" @@ p_expr_to_str body.x in *)
  let body = typed_expr_infer ctx body in
  let fty = Nt.construct_arr_tp (List.map _get_ty params, body.ty) in
  { params; local_vars; body } #: fty

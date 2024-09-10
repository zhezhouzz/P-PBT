open Syntax
open P_func_typing
open P_state_typing

type t = Nt.t

let try_func_typing l =
  List.filter_map
    (fun (fname, _) ->
      match fname.ty with Nt.Ty_unknown -> None | ty -> Some fname.x #: ty)
    l

let func_infer_add_to_ctx (ctx : t ctx) (fname, f) =
  let ctx, fname, f =
    match fname.ty with
    | Nt.Ty_unknown ->
        let f = func_infer ctx f in
        let fname = fname.x #: f.ty in
        (add_to_right ctx fname, fname, f)
    | ty ->
        let f = func_check ctx f ty in
        let fname = fname.x #: f.ty in
        (ctx, fname, f)
  in
  (ctx, (fname, f.x))

let machine_infer (ctx : t ctx)
    ({ name; local_vars; local_funcs; states } : t p_machine_decl) :
    t p_machine_decl =
  let local_vars = List.map (Nt.__force_typed [%here]) local_vars in
  let ctx = add_to_rights ctx local_vars in
  let ctx = add_to_rights ctx (try_func_typing local_funcs) in
  let ctx, local_funcs =
    List.fold_left
      (fun (ctx, fs) f ->
        let ctx, f = func_infer_add_to_ctx ctx f in
        (ctx, fs @ [ f ]))
      (ctx, []) local_funcs
  in
  let states = List.map (state_infer ctx) states in
  { name; local_vars; local_funcs; states }

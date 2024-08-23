open Syntax
open P_func_typing

type t = Nt.t

let state_infer (ctx : t ctx)
    ({ name; state_label; state_body } : t option p_state) : t p_state =
  let state_body =
    List.map
      (fun (name, f) ->
        let f = func_check ctx f Nt.Ty_unit in
        (name.x #: f.ty, f.x))
      state_body
  in
  { name; state_label; state_body }

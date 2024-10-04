include Syntax
include Common
(* include To_regex *)

(* include To_inst *)
include To_rty
include To_item

(* module Nt = struct *)
(*   include Nt.T *)
(*   include Nt *)
(* end *)

let layout_syn_env { event_rtyctx; gen_ctx; event_tyctx; tyctx; goal } =
  let str = "" in
  let str = spf "%s\n    tyctx:\n%s\n" str (layout_ctx Nt.layout tyctx) in
  let str =
    spf "%s\n    event_tyctx:\n%s\n" str
      (layout_ctx (fun l -> Nt.layout (Nt.Ty_record l)) event_tyctx)
  in
  let str =
    spf "%s\n    gen_ctx:\n%s\n" str (layout_ctx string_of_bool gen_ctx)
  in
  let str =
    spf "%s\n    event_rtyctx:\n%s\n" str (layout_ctx layout_haft event_rtyctx)
  in
  let str =
    spf "%s\n    goal:\n%s\n" str
      (match goal with None -> "none" | Some srl -> layout_syn_goal srl)
  in
  str

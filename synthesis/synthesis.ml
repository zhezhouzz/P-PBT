open Language
open Zdatatype
open Refine
open MkTerm

let mk_synthesis_goal (env : syn_env) =
  let qvs, prop =
    match env.goal with
    | None -> _die_with [%here] "no goal"
    | Some { qvs; prop } -> (qvs, prop)
  in
  (* let rctx = *)
  (*   add_to_rights emp *)
  (*     (List.map (fun x -> x.x #: { nt = x.ty; phi = mk_true }) qvs) *)
  (* in *)
  let reg = smart_negate prop in
  let op_names = List.map _get_x (ctx_to_list env.event_tyctx) in
  let reg =
    desugar env.event_tyctx (SyntaxSugar (CtxOp { op_names; body = reg }))
  in
  let reg = delimit_context reg in
  let () = Printf.printf "Original Reg: %s\n" (layout_symbolic_regex reg) in
  (Gamma.{ bvs = qvs; bprop = mk_true }, SFA.regex_to_raw reg)

let synthesize env goal =
  let* gamma, plan = deductive_synthesis_reg env goal in
  let () = Printf.printf "Result: %s\n" (Plan.layout_plan plan) in
  let term = instantiation env (gamma, plan) in
  Some term
(* Some (reverse_instantiation env res) *)

let syn_one env =
  match synthesize env @@ mk_synthesis_goal env with
  | None -> _die_with [%here] "synthesis fails"
  | Some term -> term

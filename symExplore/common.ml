(* open Language *)
(* open Zzdatatype.Datatype *)

let cheker = Prover.check_valid

let sat_solver prop =
  let res = Prover.check_sat_bool prop in
  res

let dummy_cheker _ = true
let dummy_sat_solver _ = true

(* type sym_explore_ctx = { *)
(*   spec_tyctx : spec_tyctx; *)
(*   world : world; *)
(*   step_bound : int; *)
(*   checker : Nt.t prop -> bool; *)
(*   sat_solver : Nt.t prop -> bool; *)
(* } *)

(* let init_explore_ctx ~spec_tyctx ~world ~step_bound ~request_bound = *)
(*   { *)
(*     spec_tyctx; *)
(*     world; *)
(*     step_bound; *)
(*     request_bound; *)
(*     checker = (fun p -> Prover.check_valid p); *)
(*     sat_solver = (fun p -> Prover.check_sat_bool p); *)
(*   } *)

(* let init_dummy_ctx ~spec_tyctx ~world ~step_bound ~request_bound = *)
(*   let ctx = init_explore_ctx ~spec_tyctx ~world ~step_bound ~request_bound in *)
(*   { ctx with sat_solver = (fun _ -> true); checker = (fun _ -> true) } *)

(* let layout_event_kindctx = *)
(*   ctx_to_list *)
(*   #> (List.split_by_comma (fun { x; ty = kind } -> *)
(*           spf "%s:%s" x @@ layout_event_kind kind)) *)

open Z3
open Solver
open Goal
open Language

type smt_result = SmtSat of Model.model | SmtUnsat | Timeout

type prover = {
  axioms : Expr.expr list;
  ctx : context;
  solver : solver;
  goal : goal;
}

let mk_prover () =
  let ctx =
    mk_context
      [
        ("model", "true");
        ("proof", "false");
        ("timeout", string_of_int (get_prover_timeout_bound ()));
      ]
  in
  let solver = mk_solver ctx None in
  let goal = mk_goal ctx true false false in
  (* TODO: choose axioms *)
  let axioms = [] in
  { ctx; axioms; solver; goal }

let _prover : prover option ref = ref None

let get_prover () =
  match !_prover with
  | Some p -> p
  | None ->
      let p = mk_prover () in
      let () = _prover := Some p in
      p

let get_ctx () = (get_prover ()).ctx

let handle_sat_result solver =
  (* let _ = printf "solver_result\n" in *)
  match check solver [] with
  | UNSATISFIABLE -> SmtUnsat
  | UNKNOWN ->
      (* raise (InterExn "time out!") *)
      (* Printf.printf "\ttimeout\n"; *)
      Timeout
  | SATISFIABLE -> (
      match Solver.get_model solver with
      | None -> failwith "never happen"
      | Some m -> SmtSat m)

let check_sat prop =
  let { goal; solver; axioms; _ } = get_prover () in
  Goal.reset goal;
  Goal.add goal (prop :: axioms);
  Solver.reset solver;
  Solver.add solver (get_formulas goal);
  let time_t, res = Sugar.clock (fun () -> handle_sat_result solver) in
  let () =
    _log_stat @@ fun _ -> Pp.printf "@{<bold>Z3 Solving time: %.2f@}\n" time_t
  in
  res

let check_sat_bool prop =
  let ctx = get_ctx () in
  let assertion = Propencoding.to_z3 ctx prop in
  let res =
    match check_sat assertion with
    | SmtUnsat -> false
    | SmtSat model ->
        ( _log "model" @@ fun _ ->
          Printf.printf "model:\n%s\n"
          @@ Sugar.short_str 1000 @@ Z3.Model.to_string model );
        true
    | Timeout ->
        (_log_queries @@ fun _ -> Pp.printf "@{<bold>SMTTIMEOUT@}\n");
        false
  in
  let () =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>SAT(%b): @} %s\n" res (layout_prop prop)
  in
  res

(** Unsat means true; otherwise means false *)
let check_valid prop =
  let ctx = get_ctx () in
  let assertion = Propencoding.to_z3 ctx (Not prop) in
  match check_sat assertion with
  | SmtUnsat -> true
  | SmtSat model ->
      ( _log "model" @@ fun _ ->
        Printf.printf "model:\n%s\n"
        @@ Sugar.short_str 1000 @@ Z3.Model.to_string model );
      false
  | Timeout ->
      (_log_queries @@ fun _ -> Pp.printf "@{<bold>SMTTIMEOUT@}\n");
      false

(* let get_int m i = *)
(*   match Model.eval m i true with *)
(*   | None -> failwith "get_int" *)
(*   | Some v -> *)
(*       (\* printf "get_int(%s)\n" (Expr.to_string i); *\) *)
(*       int_of_string @@ Arithmetic.Integer.numeral_to_string v *)

(* let get_bool_str m i = *)
(*   match Model.eval m i true with None -> "none" | Some v -> Expr.to_string v *)

(* let get_int_name ctx m name = *)
(*   get_int m @@ Arithmetic.Integer.mk_const_s ctx name *)

(* let get_pred m predexpr = *)
(*   match Model.eval m predexpr true with *)
(*   | None -> failwith "get pred" *)
(*   | Some v -> Z3aux.z3expr_to_bool v *)

(* let get_unknown_fv ctx m unknown_fv = *)
(*   List.map (fun (_, b) -> get_pred m (Boolean.mk_const_s ctx b)) unknown_fv *)

open Language
open Zdatatype
open Qtype
open Pfa

let state_expr = mk_pid state_decl

type qindex = int list

let fresh_qv nt =
  let name = Rename.unique "_w" in
  name #: nt

let world_decl world = default_world_name #: (world_to_nt world)
let world_expr world = mk_pid @@ world_decl world
let tmp_world_decl world = default_tmp_world_name #: (world_to_nt world)
let tmp_world_expr world = mk_pid @@ tmp_world_decl world

let mk_world_to_gprop_id_function_decl pfa ids (world : world) =
  let args = get_qvs_from_world world in
  let aux id =
    let qvs = compute_qvs_from_prop_id pfa (global_event_name, id) in
    mk_p_it
      (mk_p_app (pfa.p_gprop_func id) (List.map mk_pid qvs))
      (mk_return @@ mk_p_int id)
  in
  let es = List.map aux ids in
  let last = mk_return @@ mk_p_int (-1) in
  let body = mk_p_seqs es last in
  (world_to_gprop_id_function_decl, mk_p_function_decl args [] body)

let world_iter (f : pexpr StrMap.t -> pexpr) (world : world) : pexpr =
  let world_expr = world_expr world in
  let rec aux m world_expr world =
    match world with
    | WState ->
        let m = StrMap.add state_decl.x world_expr m in
        f m
    | WSingle { qv; world; _ } ->
        let value, world_expr = mk_depair world_expr in
        let m = StrMap.add qv.x value m in
        aux m world_expr world
    | WMap { qv; world; _ } ->
        mk_foreach_map_with_key qv world_expr (fun value ->
            let m = StrMap.add qv.x (mk_pid qv) m in
            aux m value world)
  in
  aux StrMap.empty world_expr world

let initial_state = 0
let initial_state_expr = mk_p_int initial_state
let world_init_function_name = "world_init"
let world_init_function_decl = world_init_function_name #: Nt.Ty_unit

let mk_world_init_function_decl ctx (world : world) =
  let rec aux world_expr (world : world) =
    match world with
    | WState -> mk_p_assign (world_expr, initial_state_expr)
    | WSingle { qv; world } ->
        let value, world_expr = mk_depair world_expr in
        (* let () = Printf.printf ".....%s\n" (layout_qv qv) in *)
        let e1 = mk_p_assign (value, qtype_choose_expr qv.ty) in
        let e2 = aux world_expr world in
        mk_p_seq e1 e2
    | WMap { qv; world } ->
        let e1 = mk_p_assign (world_expr, mk_p_default world_expr.ty) in
        let e2 =
          mk_foreach_set (qtype_domain_expr ctx qv.ty) (fun value ->
              aux (mk_p_access (world_expr, value)) world)
        in
        mk_p_seq e1 e2
    (* let world_expr = mk_p_access (world_expr, mk_pid qv) in *)
    (* let e = aux world_expr world in *)

    (* let e = *)
    (*   mk_foreach_set qv (qtype_domain_expr (abstract_type, qv.ty)) e *)
    (* in *)
    (* e *)
  in

  let body = aux (world_expr world) world in
  (world_init_function_decl, mk_p_function_decl [] [] body)

let machine_register_world pfa { name; local_vars; local_funcs; states } ids
    (world : world) =
  let () = Printf.printf "Register World: %s\n" (layout_world world) in
  {
    name;
    local_vars = world_decl world :: local_vars;
    local_funcs =
      mk_world_to_gprop_id_function_decl pfa ids world
      :: mk_world_init_function_decl pfa.spec_tyctx world
      :: local_funcs;
    states;
  }

(* let mk_int_forall_world qv world = *)
(*   WMap { qv = qv.x #: Nt.Ty_int; abstract_type = qv.ty; world } *)

(* let mk_int_exists_world qv world = *)
(*   WSingle { qv = qv.x #: Nt.Ty_int; abstract_type = qv.ty; world } *)

(* let _test_world1 = WState *)

(* let _test_world2 = *)
(*   mk_int_forall_world "a" #: (mk_p_abstract_ty "account") WState *)

(* let _test_world3 = *)
(*   mk_int_exists_world "a" #: (mk_p_abstract_ty "account") WState *)

(* let _test_world4 = *)
(*   mk_int_forall_world "s" #: (mk_p_abstract_ty "server") _test_world2 *)

(* let _test_world5 = *)
(*   mk_int_forall_world "s" #: (mk_p_abstract_ty "server") _test_world3 *)

(* let _test_world6 = *)
(*   mk_int_exists_world "s" #: (mk_p_abstract_ty "server") _test_world2 *)

(* let _test_world7 = *)
(*   mk_int_exists_world "s" #: (mk_p_abstract_ty "server") _test_world3 *)

(* let machine_register_world_test m = machine_register_world m _test_world7 *)

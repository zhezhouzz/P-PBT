open Language
open Zdatatype
open World
open PclientInit
open Pfa

(** Next world *)

let world_iter_with_transitions pfa (f : pexpr StrMap.t -> pexpr -> pexpr)
    (world : world) : pexpr =
  world_iter
    (fun m ->
      let qvs = get_qvs_from_world world in
      let qvs = List.map (fun qv -> StrMap.find "die" m qv.x) qvs in
      let state = StrMap.find "die" m state_decl.x in
      let mapping =
        mk_p_vaccess
          (pfa.p_transitions, mk_p_app world_to_gprop_id_function_decl qvs)
      in
      let mapping = mk_p_access (mapping, state) in
      f m mapping)
    world

let mk_next_world_function pfa world (kind, op) =
  let just_check_sat = "just_check_sat" #: Nt.Ty_bool in
  (* let op = "op" #: (mk_p_string_ty) in *)
  let res = "res" #: (Nt.mk_tuple [ Nt.Ty_bool; Nt.Ty_int ]) in
  let input = input_name #: op.ty in
  let func = validate_function_decl op in
  let if_valid = "if_valid" #: Nt.Ty_bool in
  let prepares =
    [
      mk_p_assign (mk_pid if_valid, mk_p_bool true);
      mk_p_assign (tmp_world_expr world, world_expr world);
    ]
  in
  let mk_one m mapping =
    let qvs = StrMap.find "die" pfa.action_qvs_map op.x in
    let qvs = List.map (fun qv -> StrMap.find "die" m qv.x) qvs in
    let state = StrMap.find "die" m state_decl.x in
    let mapping = mk_p_access (mapping, mk_p_string op.x) in
    let e11, e12 = mk_depair (mk_pid res) in
    let e2 =
      mk_p_ite e11
        (mk_p_assign (state, e12))
        (Some (mk_p_assign (mk_pid if_valid, mk_p_bool false)))
    in
    let body =
      if is_empty_record_ty op.ty then mk_p_let res (mk_p_bool true) e2
      else mk_p_let res (mk_p_app func (qvs @ [ mapping; mk_pid input ])) e2
    in
    body
  in
  let loop = world_iter_with_transitions pfa mk_one world in
  let e_just_check_sat =
    mk_p_it (mk_pid just_check_sat)
      (mk_p_seq
         (mk_p_assign (world_expr world, tmp_world_expr world))
         (mk_return (mk_pid if_valid)))
  in
  let body =
    mk_p_ite
      (mk_p_not (mk_pid if_valid))
      (mk_p_assign (world_expr world, tmp_world_expr world))
      (match kind with
      | Resp -> None
      | Hidden ->
          _failatwith __FILE__ __LINE__ "the hidden event should be eliminated"
      | Req -> Some (mk_send op (mk_pid input)))
  in
  let last = mk_return (mk_pid if_valid) in
  let body = mk_p_seqs (prepares @ [ loop; e_just_check_sat; body ]) last in
  ( (next_world_function op.x) #: Nt.Ty_unit,
    mk_p_function_decl
      (if is_empty_record_ty op.ty then [ just_check_sat ]
       else [ just_check_sat; input ])
      [ tmp_world_decl world; if_valid ]
      body )

(** get available actions *)

let get_available_actions_function pfa world =
  let res = "res" #: (mk_p_set_ty mk_p_string_ty) in
  let prepares = [ mk_p_assign (mk_pid res, action_domain_expr) ] in
  let mk_one _ mapping =
    let body =
      mk_p_assign
        (mk_pid res, mk_set_intersection (mk_pid res) @@ mk_p_map_keys mapping)
    in
    body
  in
  let loop = world_iter_with_transitions pfa mk_one world in
  let last = mk_return (mk_pid res) in
  let body = mk_p_seqs (prepares @ [ loop ]) last in
  (get_available_actions_function_decl, mk_p_function_decl [] [ res ] body)

(** check final *)

let mk_check_final_function_decl world =
  let res = "res" #: Nt.Ty_bool in
  let e =
    world_iter
      (fun m ->
        let qvs = get_qvs_from_world world in
        let qvs = List.map (fun qv -> StrMap.find "die" m qv.x) qvs in
        let state = StrMap.find "die" m state_decl.x in
        let final_states =
          mk_p_access
            (final_states_expr, mk_p_app world_to_gprop_id_function_decl qvs)
        in
        mk_p_it
          (mk_p_not (mk_p_in state final_states))
          (mk_p_vassign (res, mk_p_bool false)))
      world
  in
  let prepare = mk_p_vassign (res, mk_p_bool true) in
  let last = mk_return (mk_pid res) in
  let body = mk_p_seqs [ prepare; e ] last in
  (check_final_function_decl, mk_p_function_decl [] [ res ] body)

let machine_register_finals { name; local_vars; local_funcs; states } world ss =
  {
    name;
    local_vars = final_states_decl :: local_vars;
    local_funcs =
      mk_check_final_function_decl world
      :: mk_final_states_init_function_decl ss
      :: local_funcs;
    states;
  }

(** handle response *)

let mk_handle_function op =
  let next_world_f = next_world_function_decl op in
  if is_empty_record_ty op.ty then
    let body =
      mk_p_it
        (mk_p_app next_world_f [ mk_p_bool false ])
        (mk_p_goto loop_state_name)
    in
    let body = mk_p_seq body mk_p_error in
    ((Listen op.x) #: Nt.Ty_unit, mk_p_function_decl [] [] body)
  else
    let event = "input" #: op.ty in
    let body =
      mk_p_it
        (mk_p_app next_world_f [ mk_p_bool false; mk_pid event ])
        (mk_p_goto loop_state_name)
    in
    let body = mk_p_seq body mk_p_error in
    ((Listen op.x) #: Nt.Ty_unit, mk_p_function_decl [ event ] [] body)

(** Init state *)

let init_state_function_decl ctx =
  let _, input = Qtype.mk_qtype_init_input ctx in
  let e = mk_p_app qtype_init_function_decl [ mk_pid input ] in
  let mk f = mk_p_app f [] in
  let functions =
    [
      world_init_function_decl;
      action_domain_init_function_decl;
      final_states_init_function_decl;
      transition_init_function_decl;
    ]
  in
  let body =
    mk_p_seqs (e :: List.map mk functions) (mk_p_goto loop_state_name)
  in
  (* let () = Printf.printf "input: %s\n" (layout_qv input) in *)
  (* let () = _die_with [%here] (layout_qv input) in *)
  mk_p_function_decl [ input ] [] body

let init_state ctx =
  {
    name = init_state_name;
    state_label = [ Start ];
    state_body = [ (Entry #: Nt.Ty_unit, init_state_function_decl ctx) ];
  }

(** Loop state *)

let loop_state_function_decl request_ops response_ops =
  let e1 = mk_p_it (mk_p_app check_final_function_decl []) mk_p_halt in
  let action = "action" #: (mk_p_abstract_ty "string") in
  let mk_request_f op =
    let event = (spf "event_%s" op.x) #: op.ty in
    let print_event = mk_p_printf (spf "event %s: {0}" op.x) [ mk_pid event ] in
    let random_f = random_event_function_decl op in
    let next_world_f = next_world_function_decl op in
    mk_p_it
      (mk_p_eq (mk_p_string op.x) (mk_pid action))
      (mk_p_let event (mk_p_app random_f [])
         (mk_p_seq print_event
            (mk_p_it
               (mk_p_app next_world_f [ mk_p_bool false; mk_pid event ])
               (mk_p_goto loop_state_name))))
  in
  let request_es = List.map mk_request_f request_ops in
  let mk_response_f op =
    let event = (spf "event_%s" op.x) #: op.ty in
    let print_event = mk_p_printf (spf "event %s: {0}" op.x) [ mk_pid event ] in
    let random_f = random_event_function_decl op in
    let next_world_f = next_world_function_decl op in
    mk_p_it
      (mk_p_eq (mk_p_string op.x) (mk_pid action))
      (mk_p_let event (mk_p_app random_f [])
         (mk_p_seq print_event
            (mk_p_it
               (mk_p_not
               @@ mk_p_app next_world_f [ mk_p_bool true; mk_pid event ])
               (mk_p_goto loop_state_name))))
  in
  let response_es = List.map mk_response_f response_ops in
  let print_action = mk_p_printf "choose action: {0}" [ mk_pid action ] in
  let body =
    mk_p_let action
      (mk_random_from_seq (mk_p_app get_available_actions_function_decl []))
      (mk_p_seqs_ ((print_action :: request_es) @ response_es))
  in
  let body = mk_p_seq e1 body in
  (Entry #: Nt.Ty_unit, mk_p_function_decl [] [] body)

let loop_state ctx ops =
  let ops = List.filter (fun op -> not @@ is_empty_record_ty op.ty) ops in
  let request_ops, response_ops =
    List.partition
      (fun x ->
        match _get_force [%here] ctx.event_kindctx x.x with
        | Req -> true
        | Resp -> false
        | Hidden -> _die [%here])
      ops
  in
  let es = List.map mk_handle_function response_ops in
  {
    name = loop_state_name;
    state_label = [];
    state_body = loop_state_function_decl request_ops response_ops :: es;
  }

let machine_register_states ctx { name; local_vars; local_funcs; states } ops =
  {
    name;
    local_vars;
    local_funcs;
    states = init_state ctx :: loop_state ctx ops :: states;
  }

let machine_register_next_world { name; local_vars; local_funcs; states } world
    pfa =
  let ctx = pfa.spec_tyctx in
  let ops =
    List.map (fun (op, (vs, _)) -> op #: (mk_p_record_ty vs))
    @@ StrMap.to_kv_list pfa.actions
  in
  let ops =
    List.filter_map
      (fun x ->
        if String.equal x.x global_event_name then None
        else Some (_get_force [%here] ctx.event_kindctx x.x, x))
      ops
  in
  let next_world_decls =
    List.fold_right
      (fun op l -> mk_next_world_function pfa world op :: l)
      ops []
  in
  {
    name;
    local_vars;
    local_funcs =
      [ get_available_actions_function pfa world ]
      @ next_world_decls @ local_funcs;
    states;
  }

let machine_register_automata client m =
  (* let open SFA in *)
  let world = client.violation_world in
  let reg = client.violation in
  let pfa = concretlize_atuoamta "over" client.spec_tyctx reg in
  let m = register_pfa pfa m in
  let m = machine_register_world pfa m (IntMap.to_key_list pfa.mapping) world in
  (* let m = machine_register_d2s m pfa.d2s in *)
  (* let m = machine_register_transitions m pfa.mapping in *)
  let m = machine_register_finals m world pfa in
  let m = machine_register_actions m pfa in
  let m = machine_register_next_world m world pfa in
  let ops =
    List.map (fun (op, (vs, _)) -> op #: (mk_p_record_ty vs))
    @@ StrMap.to_kv_list pfa.actions
  in
  let m = machine_register_states client.spec_tyctx m ops in
  m

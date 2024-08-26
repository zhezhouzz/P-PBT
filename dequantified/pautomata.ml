open Language
open Zzdatatype.Datatype
open PclientInit
open Pfa
open Cex

let choose_possible_scope (cex, pfa) is_valid (qv : (Nt.t, string) typed) body =
  let e1 value = mk_p_seq (mk_p_vassign (qv, value)) body in
  let scope = Qtype.qtype_domain_expr pfa.spec_tyctx qv.ty in
  let scope =
    match Qtype.qtype_seen_buffer_declear_opt pfa.spec_tyctx qv.ty with
    | None -> scope
    | Some seen -> mk_p_app lib_set_union [ mk_pid seen; scope ]
  in
  let e2 =
    mk_foreach_set scope (fun x ->
        mk_p_seqs_ [ mk_p_vassign (qv, x); body; mk_p_it is_valid mk_p_break ])
  in
  p_option_bind (cex.p_global_qv qv) e1 (Some e2)

let mk_instantiate_action_function (cex, pfa) op =
  let qvs = StrMap.find "die" pfa.action_qvs_map op.x in
  let mapping =
    mk_p_access
      ( mk_p_vaccess (pfa.p_transitions, mk_pid cex.p_global_idx),
        mk_pid cex.p_state )
  in
  let input = input_name #: op.ty in
  let res = "res" #: (Nt.mk_tuple [ Nt.Ty_bool; Nt.Ty_int ]) in
  let is_valid, next_state = mk_depair (mk_pid res) in
  let cond =
    mk_p_app
      (validate_function_decl op)
      (List.map mk_pid qvs @ [ mapping; mk_pid input ])
  in
  let body = mk_p_it (mk_p_not is_valid) (mk_p_vassign (res, cond)) in
  let body =
    List.fold_right (choose_possible_scope (cex, pfa) is_valid) qvs body
  in
  let result =
    mk_p_tuple [ is_valid; mk_p_tuple (next_state :: List.map mk_pid qvs) ]
  in
  let body =
    mk_p_seqs_
      [ mk_p_assign (is_valid, mk_p_bool false); body; mk_return result ]
  in
  ( (instantiate_action_function_name op) #: body.ty,
    mk_p_function_decl [ input ] (res :: qvs) body )

let mk_realize_instantiated_action_function (cex, pfa) op =
  let qvs = StrMap.find "die" pfa.action_qvs_map op.x in
  let result =
    "result" #: (mk_p_tuple_ty (Nt.Ty_int :: List.map _get_ty qvs))
  in
  let next_state = mk_field_nth (mk_pid result) 0 in
  let es =
    List.mapi
      (fun i qv ->
        mk_p_assign (mk_pid qv, mk_field_nth (mk_pid result) (i + 1)))
      qvs
  in
  let update qv = p_option_set_when_none (cex.p_global_qv qv) (mk_pid qv) in
  let body =
    mk_p_seqs
      (es @ List.map update qvs)
      (mk_p_vassign (cex.p_state, next_state))
  in
  ( realize_instantiated_action_function op,
    mk_p_function_decl [ result ] qvs body )

let machine_register_instantiation (cex, pfa) m =
  let ops =
    List.map (fun (op, (vs, _)) -> op #: (mk_p_record_ty vs))
    @@ StrMap.to_kv_list pfa.actions
  in
  let ops = List.filter (fun x -> not (is_empty_record_ty x.ty)) ops in
  let instantiate_action_function_decls =
    List.map (mk_instantiate_action_function (cex, pfa)) ops
  in
  let realize_instantiated_action_function_decls =
    List.map (mk_realize_instantiated_action_function (cex, pfa)) ops
  in
  {
    m with
    local_funcs =
      m.local_funcs @ instantiate_action_function_decls
      @ realize_instantiated_action_function_decls;
  }

(** Init state *)

let init_state_function_decl (cex, pfa) =
  let ctx = pfa.spec_tyctx in
  let _, input = Qtype.mk_qtype_init_input ctx in
  let e = mk_p_app qtype_init_function_decl [ mk_pid input ] in
  let mk f = mk_p_app f [] in
  let functions =
    [
      action_domain_init_function_decl;
      cex.p_cex_init_function;
      pfa.p_transitions_init_function;
      pfa.p_final_init_function;
    ]
  in
  let body =
    mk_p_seqs (e :: List.map mk functions) (mk_p_goto loop_state_name)
  in
  (* let () = Printf.printf "input: %s\n" (layout_qv input) in *)
  (* let () = _die_with [%here] (layout_qv input) in *)
  mk_p_function_decl [ input ] [] body

let mk_instantiateres_decl pfa op =
  let qvs = StrMap.find "die" pfa.action_qvs_map op.x in
  let res =
    (spf "res_%s" op.x)
    #: (mk_p_tuple_ty
          [ Nt.Ty_bool; mk_p_tuple_ty (Nt.Ty_int :: List.map _get_ty qvs) ])
  in
  res

(** handle response *)

let mk_handle_function (cex, pfa) op =
  let real_op, f = _get_force [%here] pfa.spec_tyctx.wrapper_ctx op.x in
  let event = "input" #: op.ty in
  let real_input = "msg" #: real_op.ty in
  if is_empty_record_ty real_op.ty then
    let body = mk_p_goto loop_state_name in
    ((Listen real_op.x) #: Nt.Ty_unit, mk_p_function_decl [] [] body)
  else if is_empty_record_ty op.ty then
    let body = mk_p_goto loop_state_name in
    ((Listen real_op.x) #: Nt.Ty_unit, mk_p_function_decl [ real_input ] [] body)
  else
    let res = mk_instantiateres_decl pfa op in
    let is_valid, result = mk_depair (mk_pid res) in
    let update_buffer =
      match
        Qtype.mk_p_update_buffer_from_event_expr pfa.spec_tyctx
          (op, mk_pid event)
      with
      | None -> []
      | Some expr -> [ expr ]
    in
    let body =
      mk_p_seq (mk_p_vassign (event, mk_p_app f [ mk_pid real_input ]))
      @@ mk_p_let res
           (mk_p_app
              (fst (mk_instantiate_action_function (cex, pfa) op))
              [ mk_pid event ])
      @@ mk_p_ite is_valid
           (mk_p_seq
              (mk_p_app
                 (fst (mk_realize_instantiated_action_function (cex, pfa) op))
                 [ result ])
           @@ mk_p_goto loop_state_name)
      @@ Some mk_p_error
    in
    let body = mk_p_seqs update_buffer body in
    ( (Listen real_op.x) #: Nt.Ty_unit,
      mk_p_function_decl [ real_input ] [ event ] body )

(** mk_random_event *)

let mk_random_event_field ctx op (x, ty) =
  match get_opt ctx.field_assignment (deparse_field op.x x) with
  | Some "self" -> (x, mk_p_self)
  | Some "server" -> (x, mk_pid machine_local_server_decl)
  | Some _ -> _die_with [%here] "unknown assignment"
  | None -> (x, Qtype.qtype_choose_expr ty)

let mk_random_event_function_decl ctx op =
  if is_empty_record_ty op.ty then None
  else
    match _get_force [%here] ctx.event_kindctx op.x with
    | Resp | Hidden -> None
    | Req ->
        let vs = match op.ty with Nt.Ty_record l -> l | _ -> _die [%here] in
        let es = List.map (mk_random_event_field ctx op) vs in
        let body = mk_return @@ mk_p_record es in
        Some (random_event_function_decl op, mk_p_function_decl [] [] body)

let machine_register_random_events pfa m =
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
  let random_event_function_decls =
    List.filter_map (fun op -> mk_random_event_function_decl ctx (snd op)) ops
  in
  Register.machine_register_local_funcs random_event_function_decls m

(** Loop state *)

let loop_state_function_decl (cex, pfa) request_ops =
  let e1 = mk_p_it (mk_p_app cex.p_check_final_function []) mk_p_halt in
  let action = "action" #: (mk_p_abstract_ty "string") in
  let mk_request_f op =
    if is_empty_record_ty op.ty then
      let next_state =
        mk_p_access
          ( mk_p_access
              ( mk_p_access
                  ( mk_p_vaccess (pfa.p_transitions, mk_pid cex.p_global_idx),
                    mk_pid cex.p_state ),
                mk_p_string op.x ),
            mk_p_int 0 )
        (* NOTE: there is only one property. *)
      in
      let e = mk_p_vassign (cex.p_state, next_state) in
      mk_p_it (mk_p_eq (mk_p_string op.x) (mk_pid action))
      @@ mk_p_seqs
           [ e; mk_send pfa.spec_tyctx.wrapper_ctx op None ]
           (mk_p_goto loop_state_name)
    else
      let event = (spf "event_%s" op.x) #: op.ty in
      let print_event =
        mk_p_printf (spf "event %s: {0}" op.x) [ mk_pid event ]
      in
      let random_f = random_event_function_decl op in
      let res = mk_instantiateres_decl pfa op in
      let is_valid, result = mk_depair (mk_pid res) in
      mk_p_it (mk_p_eq (mk_p_string op.x) (mk_pid action))
      @@ mk_p_let event (mk_p_app random_f [])
      @@ mk_p_seq print_event
      @@ mk_p_let res
           (mk_p_app
              (fst (mk_instantiate_action_function (cex, pfa) op))
              [ mk_pid event ])
      @@ mk_p_seq
           (mk_p_it is_valid
           @@ mk_p_seq
                (mk_p_app
                   (fst (mk_realize_instantiated_action_function (cex, pfa) op))
                   [ result ])
                (mk_send pfa.spec_tyctx.wrapper_ctx op (Some (mk_pid event))))
      @@ mk_p_goto loop_state_name
  in
  let request_es = List.map mk_request_f request_ops in
  let print_action = mk_p_printf "choose action: {0}" [ mk_pid action ] in
  let action_expr = mk_p_app cex.p_get_available_actions_function [] in
  (* let action_expr = mk_pid action_domain_declar in *)
  let body =
    mk_p_let action (mk_random_from_seq action_expr)
    @@ mk_p_seqs_ (print_action :: request_es)
  in
  let body = mk_p_seq e1 body in
  (Entry #: Nt.Ty_unit, mk_p_function_decl [] [] body)

let mk_loop_state (cex, pfa) =
  let ops =
    List.map (fun (op, (vs, _)) -> op #: (mk_p_record_ty vs))
    @@ StrMap.to_kv_list pfa.actions
  in
  (* let ops = List.filter (fun op -> not @@ is_empty_record_ty op.ty) ops in *)
  let request_ops, response_ops =
    List.partition
      (fun x ->
        match _get_force [%here] pfa.spec_tyctx.event_kindctx x.x with
        | Req -> true
        | Resp -> false
        | Hidden -> _die [%here])
      ops
  in
  (* let () = *)
  (*   Printf.printf "request_ops: %s\n" *)
  (*   @@ List.split_by_comma layout_qv request_ops *)
  (* in *)
  (* let () = _die [%here] in *)
  let es = List.map (mk_handle_function (cex, pfa)) response_ops in
  loop_state_function_decl (cex, pfa) request_ops :: es

(** Error state *)

let mk_err_handle_function op =
  ( (Listen op.x) #: Nt.Ty_unit,
    mk_p_function_decl [] [] (mk_p_goto error_state_name) )

let mk_err_state pfa =
  let ops =
    List.map (fun (op, (vs, _)) -> op #: (mk_p_record_ty vs))
    @@ StrMap.to_kv_list pfa.actions
  in
  let ops = List.filter (fun op -> not @@ is_empty_record_ty op.ty) ops in
  let _, response_ops =
    List.partition
      (fun x ->
        match _get_force [%here] pfa.spec_tyctx.event_kindctx x.x with
        | Req -> true
        | Resp -> false
        | Hidden -> _die [%here])
      ops
  in
  let real_response_ops =
    List.map
      (fun op -> fst @@ _get_force [%here] pfa.spec_tyctx.wrapper_ctx op.x)
      response_ops
  in
  let es = List.map mk_err_handle_function real_response_ops in
  es

open Register

let machine_register_automata (client : (Nt.t prop * SFA.dfa) list client) m =
  (* let open SFA in *)
  (* let () = *)
  (*   List.iter *)
  (*     (fun (_, sfa) -> Printf.printf "sfa.state = %i\n" sfa.SFA.start) *)
  (*     client.violation *)
  (* in *)
  let pfa = concretlize_atuoamta "cex" client.spec_tyctx client.violation in
  let cex = mk_cex client in
  let m = register_pfa pfa m in
  let m = register_cex pfa cex m in
  (* let m = machine_register_d2s m pfa.d2s in *)
  (* let m = machine_register_transitions m pfa.mapping in *)
  (* let m = machine_register_finals m world pfa.finals in *)
  let m = machine_register_actions m pfa in
  let m = machine_register_random_events pfa m in
  let m = machine_register_instantiation (cex, pfa) m in
  let m =
    machine_register_init_state_with_func
      (init_state_function_decl (cex, pfa))
      m
  in
  let m = machine_register_loop_state_with_funcs (mk_loop_state (cex, pfa)) m in
  let m = machine_register_err_state_with_funcs (mk_err_state pfa) m in
  m

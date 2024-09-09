open Language
open Zdatatype
open Pfa

(* type client_basic = { *)
(*   p_response_action_domain : (Nt.t, string) typed; *)
(*   p_action_domain : (Nt.t, string) typed; *)
(*   p_validate_function : (Nt.t, string) typed -> (Nt.t, string) typed; *)
(*   mk_send : (Nt.t, string) typed -> pexpr -> pexpr; *)
(* } *)

let action_name_mapping_expr = mk_pid @@ action_name_mapping_decl

(** validate an event;
    note that the transition map is not complete -- if the key not found means false
*)

let total_mapping_decl =
  "total_mapping"
  #: (mk_p_map_ty mk_p_string_ty @@ mk_p_map_ty Nt.Ty_int Nt.Ty_int)

let mk_validate_function pfa op size =
  if is_empty_record_ty op.ty then None
  else
    let next_state = "next_state" #: Nt.Ty_int in
    let if_valid = "if_valid" #: Nt.Ty_bool in
    let mapping = mk_p_vaccess (total_mapping_decl, mk_p_string op.x) in
    let input = input_name #: op.ty in
    let prepare = mk_p_assign (mk_pid if_valid, mk_p_bool false) in
    (* let e = mk_foreach_map (mk_pid mapping) (fun action_id) *)
    let mk_one i s prop_id =
      let prop_func = pfa.p_prop_func (op, prop_id) in
      let qvs = compute_qvs_from_prop_id pfa (op.x, prop_id) in
      let condition = mk_p_app prop_func (List.map mk_pid (qvs @ [ input ])) in
      let tbranch = mk_return @@ mk_p_tuple [ mk_p_bool true; s ] in
      mk_p_it (mk_p_eq (mk_pid i) (mk_p_int prop_id))
      @@ mk_p_it condition tbranch
    in
    let check_valid =
      mk_foreach_map mapping (fun i s ->
          mk_p_seqs_ @@ List.init size (mk_one i s))
    in
    let return =
      mk_return (mk_p_tuple (List.map mk_pid [ if_valid; next_state ]))
    in
    let check_key_valid =
      mk_p_in (mk_p_string op.x) @@ mk_p_map_keys @@ mk_pid total_mapping_decl
    in
    let body =
      mk_p_seq prepare @@ mk_p_seq (mk_p_it check_key_valid check_valid) return
    in
    let qvs = StrMap.find "die" pfa.action_qvs_map op.x in
    Some
      ( validate_function_decl op,
        mk_p_function_decl
          (qvs @ [ total_mapping_decl; input ])
          [ next_state; if_valid ] body )

(** send *)

let mk_send spec_ctx op payload =
  let _, f = get_real_op spec_ctx op.x in
  let dest = mk_pid server_domain_decl in
  match payload with
  | None -> mk_p_app f [ mk_p_this; dest ]
  | Some payload ->
      (* let l = *)
      (*   match remove_server_field_record_type op.ty with *)
      (*   | Nt.Ty_record l -> l *)
      (*   | _ -> _die [%here] *)
      (* in *)
      (* let l = match op.ty with Nt.Ty_record l -> l | _ -> _die [%here] in *)
      (* let payload = *)
      (*   mk_p_record @@ List.map (fun (name, _) -> (name, mk_field event name)) l *)
      (* in *)
      mk_p_app f [ mk_p_this; dest; payload ]

let action_domain_expr = mk_pid action_domain_declar

let action_domain_init spec_ctx actions =
  let l = StrMap.to_key_list actions in
  let response =
    List.filter
      (fun op ->
        match _get_force [%here] spec_ctx.event_kindctx op with
        | Resp -> true
        | Req | Hidden -> false)
      l
  in
  let es =
    List.map (fun op -> mk_p_add_set action_domain_expr (mk_p_string op)) l
  in
  let es' =
    List.map
      (fun op ->
        mk_p_add_set (mk_pid p_response_actions_domain) (mk_p_string op))
      response
  in
  let body = mk_p_seqs (es @ es') mk_return_void in
  (action_domain_init_function_decl, mk_p_function_decl [] [] body)

(** mk_action *)

let machine_register_actions { name; local_vars; local_funcs; states } pfa =
  let actions_decls =
    List.filter_map (fun x -> x)
    @@ StrMap.fold
         (fun op (vs, phis) l ->
           let op = op #: (mk_p_record_ty vs) in
           mk_validate_function pfa op (List.length phis) :: l)
         pfa.actions []
  in
  {
    name;
    local_vars = p_response_actions_domain :: action_domain_declar :: local_vars;
    local_funcs =
      [ action_domain_init pfa.spec_tyctx pfa.actions ]
      @ actions_decls @ local_funcs;
    states;
  }

let final_states_expr = mk_pid final_states_decl

let mk_final_states_init_function_decl ss =
  let m =
    IntMap.map
      (fun ss final_states_expr ->
        let ss = List.of_seq @@ StateSet.to_seq ss in
        let e =
          mk_p_assign (final_states_expr, mk_p_default final_states_expr.ty)
        in
        let es =
          List.map (fun s -> mk_p_add_set final_states_expr (mk_p_int s)) ss
        in
        mk_p_seqs_ (e :: es))
      ss
  in
  let body = init_p_int_map m final_states_expr in
  (final_states_init_function_decl, mk_p_function_decl [] [] body)

let file_register_abstract_types ctx items =
  let l =
    List.map
      (fun x ->
        match x.ty with
        | CBaseType { superty; _ } -> PTypeDecl x.x #: superty
        | CEnumType { enum_elems; _ } -> PEnumDecl (x.x, enum_elems))
      (ctx_to_list ctx.abstract_tyctx)
  in
  items @ l

let file_register_events ctx items =
  let l = ctx_to_list ctx.event_tyctx in
  let l =
    List.filter_map
      (fun { x; ty = tys } ->
        match _get_force [%here] ctx.event_kindctx x with
        | Req ->
            (* let tys = (source_field_decl.x, source_field_decl.ty) :: tys in *)
            Some x #: (Nt.Ty_record tys)
        | Resp -> Some x #: (Nt.Ty_record tys)
        | Hidden -> None
        (* NOTE: the hidden events are already defined some place else. *))
      l
  in
  let l = List.map (fun x -> PEventDecl x) l in
  items @ l

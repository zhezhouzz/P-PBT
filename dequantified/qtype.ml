open Language
(* open Zzdatatype.Datatype *)

let qSeenBuffer = spf "%s_seen"
let qDomain = spf "%s_domain"
let default_qtype = [ mk_p_abstract_ty "int"; mk_p_abstract_ty "bool" ]

let default_int_domain_init_function =
  "mk_total_int_set" #: (mk_p_set_ty Nt.Ty_int)

let default_bool_domain_init_function =
  "mk_total_bool_set" #: (mk_p_set_ty Nt.Ty_bool)

let domain_name spec_ctx nt =
  let cty = _get_force [%here] spec_ctx.abstract_tyctx (Nt.layout nt) in
  match cty with
  | CBaseType { superty; use_config = false } ->
      Nt.layout superty |> qDomain (* builtin type *)
  | CBaseType { use_config = true; _ } ->
      Nt.layout nt |> qDomain (* abstract type *)
  | CEnumType _ -> Nt.layout nt |> qDomain (* abstract type *)

(* match nt with *)
(* | Nt.Ty_constructor (name, []) -> name ^ qDomain (\* abstract type *\) *)
(* | Nt.Ty_int | Nt.Ty_bool -> Nt.layout nt ^ qDomain (\* builtin type *\) *)
(* | _ -> *)
(*     let () = Printf.printf "%s\n" (Nt.layout nt) in *)
(*     _die [%here] *)

let qtype_seen_buffer_declear_opt spec_ctx nt =
  (* we don't care about machine type *)
  if String.equal "machine" (Nt.layout nt) then None
  else if String.equal "bool" (Nt.layout nt) then None
  else
    (* let () = Printf.printf "Check: %s\n" (Nt.layout nt) in *)
    let cty = _get_force [%here] spec_ctx.abstract_tyctx (Nt.layout nt) in
    match cty with
    | CBaseType { use_config = false; _ } ->
        Some (spf "%s_seen" (Nt.layout nt)) #: (mk_p_set_ty nt)
    | _ -> None

let qtype_seen_buffer_declear spec_ctx nt =
  match qtype_seen_buffer_declear_opt spec_ctx nt with
  | None -> _die_with [%here] "should not use buffer"
  | Some x -> x

let qtype_domain_declear ctx nt = (domain_name ctx nt) #: (mk_p_set_ty nt)
let qtype_domain_expr ctx nt = mk_pid @@ qtype_domain_declear ctx nt
let qtype_int_domain_declear = ("int" |> qDomain) #: (mk_p_set_ty Nt.Ty_int)
let qtype_bool_domain_declear = ("bool" |> qDomain) #: (mk_p_set_ty Nt.Ty_bool)

(* let p_update_buffer_from_event_function op = *)
(*   (spf "update_buffer_from_event_%s" op.x) #: Nt.Ty_unit *)

let mk_p_update_buffer_from_event_expr spec_ctx (op, event_expr) =
  let feilds = match op.ty with Nt.Ty_record l -> l | _ -> _die [%here] in
  let feilds =
    List.filter_map
      (fun (name, nt) ->
        let* domain = qtype_seen_buffer_declear_opt spec_ctx nt in
        Some (mk_p_add_set (mk_pid domain) (mk_field event_expr name)))
      feilds
  in
  match feilds with [] -> None | es -> Some (mk_p_seqs_ es)

let fresh_qname nt =
  let name = Rename.unique (Nt.layout nt) in
  name #: nt

let qtype_iter ctx (f : pexpr -> pexpr) (qty : Nt.t) : pexpr =
  let set = qtype_domain_expr ctx qty in
  mk_foreach_set set f

let mk_index_set_function_decl =
  "mk_index_set"
  #: (Nt.mk_arr
        (mk_p_seq_ty (mk_p_abstract_ty "machine"))
        (mk_p_set_ty Nt.int_ty))

(* NOTE: add machine_local_server_decl *)
let mk_qtype_init_input ctx =
  let qtypes =
    List.filter_map
      (function
        | { x; ty = CBaseType { use_config = true; _ } } ->
            Some (mk_p_abstract_ty x)
        | _ -> None)
      (ctx_to_list ctx.abstract_tyctx)
  in
  let vs = List.map (qtype_domain_declear ctx) qtypes in
  let vs = server_domain_decl :: vs in
  let input = "input" #: (mk_p_record_ty vs) in
  (vs, input)

let mk_qtype_init_function_decl ctx =
  let vs, input = mk_qtype_init_input ctx in
  let es =
    List.map (fun x -> mk_p_vassign (x, mk_field (mk_pid input) x.x)) vs
  in
  let init_enum name enum_elems =
    List.map
      (fun y ->
        let y = mk_pid y #: (mk_p_abstract_ty name) in
        let x = qtype_domain_declear ctx y.ty in
        mk_p_add_set (mk_pid x) y)
      enum_elems
  in
  let default_init nt =
    match Nt.layout nt with
    | "int" ->
        mk_p_vassign
          ( qtype_int_domain_declear,
            mk_p_app default_int_domain_init_function [] )
    | "bool" ->
        mk_p_vassign
          ( qtype_bool_domain_declear,
            mk_p_app default_bool_domain_init_function [] )
    | _ as ty_name -> _die_with [%here] ty_name
  in
  let default_es = List.map default_init default_qtype in
  let es' =
    List.map
      (function
        | { x; ty = CEnumType { enum_elems; _ } } -> init_enum x enum_elems
        | _ -> [])
      (ctx_to_list ctx.abstract_tyctx)
  in
  let body = mk_p_seqs_ @@ List.concat (default_es :: es :: es') in
  (qtype_init_function_decl, mk_p_function_decl [ input ] [] body)

let qtype_choose_function_decl nt = ("qtype_choose_" ^ Nt.layout nt) #: nt

let make_qtype_choose_function_decls ctx nt =
  let domain_decl = qtype_domain_declear ctx nt in
  let res = "res" #: nt in
  let mk_choose decl =
    mk_p_vassign
      (res, mk_p_app "choose" #: (Nt.mk_arr (mk_p_set_ty nt) nt) [ mk_pid decl ])
  in
  let body =
    match qtype_seen_buffer_declear_opt ctx nt with
    | None -> mk_choose domain_decl
    | Some buffer ->
        (* let () = Printf.printf "Buffer: %s\n" (layout_qv buffer) in *)
        mk_p_ite
          (mk_p_app lib_set_is_empty [ mk_pid buffer ])
          (mk_choose domain_decl)
        @@ Some
             (mk_p_ite mk_random_bool (mk_choose domain_decl)
             @@ Some (mk_choose buffer))
  in
  let body = mk_p_seq body (mk_return @@ mk_pid res) in
  (qtype_choose_function_decl nt, mk_p_function_decl [] [ res ] body)

let qtype_choose_expr nt = mk_p_app (qtype_choose_function_decl nt) []

let get_qtypes_from_abstract_ctx ctx =
  List.filter_map
    (function
      | { x; ty = CBaseType { use_config = true; _ } } ->
          Some (mk_p_abstract_ty x)
      | { x; ty = CEnumType _ } -> Some (mk_p_abstract_ty x)
      | _ -> None)
    (ctx_to_list ctx.abstract_tyctx)

let machine_register_qtypes client { name; local_vars; local_funcs; states } =
  let qtypes = get_qtypes_from_abstract_ctx client.spec_tyctx in
  let total_types =
    List.map (fun x -> mk_p_abstract_ty x.x)
    @@ ctx_to_list client.spec_tyctx.abstract_tyctx
  in
  let buffer_declears =
    List.filter_map
      (qtype_seen_buffer_declear_opt client.spec_tyctx)
      total_types
  in
  (* let () = *)
  (*   List.iter *)
  (*     (fun qv -> Printf.printf "buffer: %s\n" @@ layout_qv qv) *)
  (*     buffer_declears *)
  (* in *)
  (* let () = _die [%here] in *)
  let declears =
    qtype_int_domain_declear :: qtype_bool_domain_declear
    :: List.map (qtype_domain_declear client.spec_tyctx) qtypes
  in
  let random_func_decls =
    List.map (make_qtype_choose_function_decls client.spec_tyctx) total_types
  in
  {
    name;
    local_vars = local_vars @ (server_domain_decl :: declears) @ buffer_declears;
    local_funcs =
      local_funcs
      @ [ mk_qtype_init_function_decl client.spec_tyctx ]
      @ random_func_decls;
    states;
  }

(* let machine_register_qtypes_test m = *)
(*   machine_register_qtypes m [ "server" #: Nt.Ty_int; "account" #: Nt.Ty_int ] *)

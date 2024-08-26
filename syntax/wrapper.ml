let rec is_p_prim_type = function
  | Nt.Ty_bool | Nt.Ty_int -> true
  | Nt.Ty_record l -> List.for_all (fun (_, ty) -> is_p_prim_type ty) l
  | Nt.Ty_tuple l -> List.for_all is_p_prim_type l
  | Nt.Ty_constructor (name, []) when String.equal name "machine" -> true
  | Nt.Ty_constructor (name, [ nt ]) ->
      (String.equal "set" name || String.equal "req" name) && is_p_prim_type nt
  | Nt.Ty_constructor (name, [ nt1; nt2 ]) ->
      String.equal "map" name && is_p_prim_type nt1 && is_p_prim_type nt2
  | _ -> false

open Ast
open Zzdatatype.Datatype

let get_absty nt =
  let rec aux = function
    | Nt.Ty_bool | Nt.Ty_int -> []
    | Nt.Ty_record l -> List.concat_map (fun (_, ty) -> aux ty) l
    | Nt.Ty_tuple l -> List.concat_map aux l
    | Nt.Ty_constructor (name, []) when String.equal name "machine" -> []
    | Nt.Ty_constructor (name, []) -> [ name ]
    | Nt.Ty_constructor (_, [ nt ]) -> aux nt
    | Nt.Ty_constructor (_, [ nt1; nt2 ]) -> aux nt1 @ aux nt2
    | _ -> _die [%here]
  in
  List.slow_rm_dup String.equal (aux nt)

let instantiate_absty (x, ty) nt =
  let rec aux nt =
    match nt with
    | Nt.Ty_bool | Nt.Ty_int -> nt
    | Nt.Ty_record l -> Nt.Ty_record (List.map (fun (x, nt') -> (x, aux nt')) l)
    | Nt.Ty_tuple l -> Nt.Ty_tuple (List.map aux l)
    | Nt.Ty_constructor (name, []) when String.equal name x -> ty
    | Nt.Ty_constructor (_, []) -> nt
    | Nt.Ty_constructor (name, [ nt ]) -> Nt.Ty_constructor (name, [ aux nt ])
    | Nt.Ty_constructor (name, [ nt1; nt2 ]) ->
        Nt.Ty_constructor (name, [ aux nt1; aux nt2 ])
    | _ -> _die [%here]
  in
  aux nt

let instantiate_abstys = List.fold_right instantiate_absty

type result = EnumType of string | Dependent of string list | NType of Nt.t

let get_type_from_wrapper_opt name code =
  let res =
    List.filter_map
      (function
        | WrapperEnum { enum_name; _ } when String.equal enum_name name ->
            Some (mk_p_abstract_ty enum_name, [])
        | WrapperTypeAlias { type_name; alias_type }
          when String.equal type_name name ->
            Some (alias_type, get_absty alias_type)
        | WrapperEventDecl { event_name; event_type }
          when String.equal event_name name ->
            Some (event_type, get_absty event_type)
        | WrapperMachineDecl { machine_name; _ }
          when String.equal machine_name name ->
            Some (mk_p_machine_ty, [])
        | WrapperSpecEventDecl { event_name; spec_event_type; p_event_name; _ }
          when String.equal event_name name ->
            Some (spec_event_type, [ p_event_name ])
        | _ -> None)
      code
  in
  match res with
  | [] -> _die_with [%here] (spf "cannot find %s" name)
  | [ res ] -> res
  | l -> (
      let l' =
        List.filter (function Nt.Ty_record _, _ -> true | _ -> false) l
      in
      match l' with
      | [ res ] -> res
      | _ ->
          let () =
            Printf.printf "multiple(%s): %s\n" name
              (List.split_by_comma (fun (nt, _) -> Nt.layout nt) l)
          in
          _die [%here])

let filter_wrapper f code =
  let aux = function
    | WrapperEnum { enum_name; _ } -> f enum_name
    | WrapperTypeAlias { type_name; _ } -> f type_name
    | WrapperEventDecl { event_name; _ } -> f event_name
    | WrapperMachineDecl { machine_name; _ } -> f machine_name
    | WrapperSpecEventDecl _ -> true
    | ReqResp _ -> true
    | Dummy -> false
  in
  List.filter aux code

let get_spec_event_names code =
  let names =
    List.filter_map
      (function
        | WrapperSpecEventDecl { p_event_name; _ } -> Some p_event_name
        | _ -> None)
      code
  in
  names

let instantiate_by_env (enum_names, env) ty =
  let l = get_absty ty in
  let l = List.substract String.equal l enum_names in
  let l = List.map (fun x -> (x, StrMap.find "die" env x)) l in
  let ty = instantiate_abstys l ty in
  ty

let env_reduction enum_names (env : Nt.t StrMap.t) =
  let rec aux env names =
    match names with
    | [] -> env
    | name :: names -> (
        if List.exists (String.equal name) enum_names then aux env names
        else
          let ty = StrMap.find "die" env name in
          match get_absty ty with
          | [] -> aux env names
          | names' ->
              let env = aux env names' in
              let ty = instantiate_by_env (enum_names, env) ty in
              let env = StrMap.update name (function _ -> Some ty) env in
              aux env names)
  in
  aux env (StrMap.to_key_list env)

let simplify_wrapper (code : p_wrapper list) spec_code =
  let names = get_spec_event_names spec_code in
  let rec aux (env : Nt.t StrMap.t) (fv : string list) =
    match fv with
    | [] -> env
    | name :: fv ->
        if StrMap.mem name env then aux env fv
        else
          let nt, fv' = get_type_from_wrapper_opt name code in
          let env = StrMap.add name nt env in
          aux env (fv' @ fv)
  in
  let env = aux StrMap.empty names in
  let enum_names =
    List.filter_map
      (function WrapperEnum { enum_name; _ } -> Some enum_name | _ -> None)
      code
  in
  let simp_env = env_reduction enum_names env in
  let names = StrMap.to_key_list env in
  ( env,
    simp_env,
    filter_wrapper (fun name -> List.exists (String.equal name) names) code )

let code_reduction env (code : p_wrapper list) =
  let enum_names =
    List.filter_map
      (function WrapperEnum { enum_name; _ } -> Some enum_name | _ -> None)
      code
  in
  let env = env_reduction enum_names env in
  let code =
    List.map
      (fun item ->
        match item with
        | WrapperEnum _ -> item
        | WrapperTypeAlias { type_name; alias_type } ->
            WrapperTypeAlias
              {
                type_name;
                alias_type = instantiate_by_env (enum_names, env) alias_type;
              }
        | WrapperEventDecl { event_name; event_type } ->
            WrapperEventDecl
              {
                event_name;
                event_type = instantiate_by_env (enum_names, env) event_type;
              }
        | WrapperMachineDecl _ -> item
        | WrapperSpecEventDecl _ -> item
        | ReqResp _ -> item
        | Dummy -> item)
      code
  in
  (env, code)

let match_field enum_names env p_event_type name =
  let rec aux ty =
    (* let () = Printf.printf "match_field: %s\n" (Nt.layout ty) in *)
    match ty with
    | Nt.Ty_record l -> (
        match List.find_opt (fun (x, _) -> String.equal name x) l with
        | Some (x, ty) -> Some ([ x ], ty)
        | _ ->
            List.fold_left
              (fun res (x, ty) ->
                match res with
                | None ->
                    let* path, ty = aux ty in
                    Some (x :: path, ty)
                | Some _ -> res)
              None l)
    | Nt.Ty_constructor (name, []) -> (
        if List.exists (String.equal name) enum_names then None
        else
          match StrMap.find_opt env name with Some ty -> aux ty | None -> None)
    | _ -> None
  in
  match aux p_event_type with
  | None -> _die_with [%here] @@ spf "cannot find filed %s" name
  | Some res -> res

let to_p_request_decl name = (spf "to_p_request_%s" name.x) #: name.ty
let from_p_response_decl name = (spf "from_p_response_%s" name.x) #: name.ty
let mk_event_access x path = List.fold_left mk_field (mk_pid x) path

type wrapper = {
  original_event : (Nt.t, string) typed;
  decl : (Nt.t, string) typed;
  imp : Nt.t p_func;
}

(** We add a client and server filed *)
let mk_event_to_p_event (x, p_x, l) =
  let client = "client" #: mk_p_machine_ty in
  let server = machine_local_server_decl in
  let event = "sevent" #: x.ty in
  let pEvent = "pEvent" #: p_x.ty in
  let es =
    List.map
      (fun (x, path) ->
        (* let () = Printf.printf "%s = %s\n" x (StrList.to_string path) in *)
        mk_p_assign (mk_event_access pEvent path, mk_event_access event [ x ]))
      l
  in
  let body = mk_p_seqs es (mk_return (mk_pid pEvent)) in
  let params =
    match event.ty with
    | Nt.Ty_record [] -> [ client; server ]
    | _ -> [ client; server; event ]
  in
  ( x.x,
    {
      original_event = p_x;
      decl = to_p_request_decl p_x.x #: x.ty;
      imp = Pmachine.mk_p_function_decl params [ pEvent ] body;
    } )

let mk_p_event_to_event (x, p_x, l) =
  let event = "sevent" #: x.ty in
  let pEvent = "pEvent" #: p_x.ty in
  (* let () = *)
  (*   List.iter *)
  (*     (fun (name, path) -> *)
  (*       Printf.printf "%s = %s\n" name (StrList.to_string path)) *)
  (*     l *)
  (* in *)
  let es =
    List.map
      (fun (x, path) ->
        mk_p_assign (mk_event_access event [ x ], mk_event_access pEvent path))
      l
  in
  let body = mk_p_seqs es (mk_return (mk_pid event)) in
  ( x.x,
    {
      original_event = p_x;
      decl = from_p_response_decl p_x;
      imp = Pmachine.mk_p_function_decl [ pEvent ] [ event ] body;
    } )

let mk_wrapper enum_names env (event_name, p_event_name) =
  (* let () = Printf.printf "%s\n" (StrList.to_string (StrMap.to_key_list env)) in *)
  let p_event_type =
    StrMap.find
      (spf "cannot find p_event_name: %s" p_event_name.x)
      env p_event_name.x
  in
  let spec_event_type = event_name.ty in
  let fields =
    match spec_event_type with Nt.Ty_record l -> l | _ -> _die [%here]
  in
  let fields =
    List.map
      (fun (x, _) ->
        let path, _ = match_field enum_names env p_event_type x in
        (* let () = *)
        (*   _assert __FILE__ __LINE__ "check wrapper type match" (Nt.eq ty ty') *)
        (* in *)
        (x, path))
      fields
  in
  (* let () = *)
  (*   List.iter *)
  (*     (fun (x, path) -> *)
  (*       Printf.printf "%s.%s = pevent.%s\n" event_name.x x *)
  (*         (List.split_by "." (fun x -> x) path)) *)
  (*     fields *)
  (* in *)
  (event_name, p_event_name, fields)

let mk_wrappers (_, env, code) =
  let enum_names =
    List.filter_map
      (function WrapperEnum { enum_name; _ } -> Some enum_name | _ -> None)
      code
  in
  let wrappers =
    List.filter_map
      (function
        | WrapperSpecEventDecl
            { event_name; p_event_name; event_kind; spec_event_type } ->
            let event_name = event_name #: spec_event_type in
            let p_event_name =
              p_event_name #: (StrMap.find "die" env p_event_name)
            in
            Some
              (event_kind, mk_wrapper enum_names env (event_name, p_event_name))
        | _ -> None)
      code
  in
  let requests =
    List.filter_map (function Req, x -> Some x | _, _ -> None) wrappers
  in
  let response =
    List.filter_map (function Resp, x -> Some x | _, _ -> None) wrappers
  in
  let decls =
    List.map mk_event_to_p_event requests
    @ List.map mk_p_event_to_event response
  in
  let tab = StrMap.from_kv_list decls in
  tab

let to_conversion_code (pcode, _, tab) =
  let strs =
    StrMap.map
      (fun { decl; imp; _ } ->
        Backend.layout_global_function init_spec_tyctx 0 (decl, imp))
      tab
  in
  let pcode =
    List.filter
      (function
        | WrapperEnum _ | WrapperTypeAlias _ | WrapperEventDecl _ -> true
        | _ -> false)
      pcode
  in
  (* let code = *)
  (*   List.filter_map *)
  (*     (function *)
  (*       | WrapperSpecEventDecl { event_name; spec_event_type; _ } -> *)
  (*           Some (WrapperEventDecl { event_name; event_type = spec_event_type }) *)
  (*       | _ -> None) *)
  (*     spec_code *)
  (* in *)
  spf "%s\n%s"
    (Backend.layout_p_wapper_decls pcode)
    (List.split_by "" (fun x -> x) (StrMap.to_value_list strs))

let tab_to_wrapper_ctx tab =
  Typectx
    (List.map (fun (x, { original_event; decl; _ }) ->
         x #: (original_event, decl))
    @@ StrMap.to_kv_list tab)

let code_to_item = function
  | WrapperEnum { enum_name; elems } ->
      Some
        (MAbstractType
           enum_name #: (CEnumType { enum_name; enum_elems = elems }))
  | WrapperTypeAlias { type_name; alias_type } ->
      Some
        (MAbstractType
           type_name #: (CBaseType { superty = alias_type; use_config = false }))
  | WrapperEventDecl _ -> None
  | WrapperMachineDecl _ -> None
  | WrapperSpecEventDecl { event_name; spec_event_type; event_kind; _ } ->
      Some (MEventDecl { ev = event_name #: spec_event_type; event_kind })
  | ReqResp _ -> None
  | Dummy -> None

let code_to_items = List.filter_map code_to_item

let code_to_reqresp_ctx code =
  let l =
    List.filter_map
      (function ReqResp { req; resp } -> Some req #: resp | _ -> None)
      code
  in
  add_to_rights emp l

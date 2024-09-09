open Ast
open Zdatatype
open Common

let mk_spec_tyctx_one ctx = function
  | MFieldAssign { field; assignment } ->
      {
        ctx with
        field_assignment = add_to_right ctx.field_assignment field #: assignment;
      }
  | MValDecl x -> { ctx with tyctx = add_to_right ctx.tyctx x }
  | MAbstractType x -> (
      (* NOTE: only enum, int, bool, and alias type can be controlled by user. *)
      match x.ty with
      | CBaseType { superty = Nt.Ty_int; _ }
      | CBaseType { superty = Nt.Ty_bool; _ }
      | CBaseType { superty = Nt.Ty_constructor (_, []); _ }
      | CEnumType _ ->
          { ctx with abstract_tyctx = add_to_right ctx.abstract_tyctx x }
      | _ -> ctx)
  | MEventDecl { ev; event_kind } -> (
      match ev.ty with
      | Nt.Ty_record l ->
          {
            ctx with
            event_tyctx = add_to_right ctx.event_tyctx ev.x #: l;
            event_kindctx = add_to_right ctx.event_kindctx ev.x #: event_kind;
          }
      | _ -> _die [%here])
  | MRegex { name; _ } ->
      { ctx with regex_tyctx = add_to_right ctx.regex_tyctx name }
  | MClient _ -> ctx

let mk_spec_ctx (env, wrapper_ctx, reqresp_ctx) code =
  let p_tyctx = ctx_from_map env in
  let spec_ctx = List.fold_left mk_spec_tyctx_one init_spec_tyctx code in
  let abs_names =
    List.slow_rm_dup String.equal
    @@ List.concat_map (fun l -> List.concat_map (fun x -> get_absty x.ty) l.ty)
    @@ ctx_to_list spec_ctx.event_tyctx
  in
  let abstract_tyctx =
    filter_ctx_name
      (fun x -> List.exists (String.equal x) abs_names)
      spec_ctx.abstract_tyctx
  in
  { spec_ctx with abstract_tyctx; wrapper_ctx; reqresp_ctx; p_tyctx }

let add_config_to_spec_tyctx ctx names =
  let abstract_tyctx =
    Typectx.map_ctx_typed
      (fun x ->
        match x.ty with
        | CBaseType { superty; _ } when List.exists (String.equal x.x) names ->
            x.x #: (CBaseType { superty; use_config = true })
        | _ -> x)
      ctx.abstract_tyctx
  in
  { ctx with abstract_tyctx }

let layout_event_kind = function
  | Req -> "request"
  | Resp -> "response"
  | Hidden -> "hidden"

let get_real_op { wrapper_ctx; p_tyctx; _ } op =
  let real_op, f = _get_force [%here] wrapper_ctx op in
  let ty =
    (* HACK: some p event doesn't return record type *)
    match _get_force [%here] p_tyctx real_op.x with
    | Nt.Ty_record [ { ty = Nt.Ty_constructor (name, []); _ } ]
      when String.equal "tLsn" name ->
        mk_p_abstract_ty "tLsn"
    | Nt.Ty_record [ { ty = Nt.Ty_bool; _ } ] -> Nt.Ty_bool
    | _ as t -> t
  in
  let real_op = real_op.x #: ty in
  (real_op, f)

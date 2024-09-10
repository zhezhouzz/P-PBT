open Syntax
open P_id_typing
open P_constant_typing
open Sugar

type t = Nt.t

let rec typed_expr_check (ctx : t ctx) (expr : (t, t p_expr) typed) (ty : t) :
    (t, t p_expr) typed =
  let ty =
    match expr.ty with
    | Nt.Ty_unknown -> ty
    | ty' -> Nt._type_unify [%here] ty' ty
  in
  expr_check ctx expr.x ty

and typed_expr_infer (ctx : t ctx) (expr : (t, t p_expr) typed) :
    (t, t p_expr) typed =
  match expr.ty with
  | Nt.Ty_unknown -> expr_infer ctx expr.x
  | ty' -> expr_check ctx expr.x ty'

and expr_check (ctx : t ctx) (expr : t p_expr) (ty : t) : (t, t p_expr) typed =
  match (expr, ty) with
  | PThis, _ ->
      let tmp = id_check ctx "this" ty in
      PThis #: tmp.ty
  | PNull, _ -> PNull #: ty
  | Pid id, _ ->
      let id = typed_id_check ctx id ty in
      (Pid id) #: id.ty
  | PConst c, _ ->
      let ty = Nt._type_unify [%here] (infer_constant c) ty in
      (PConst c) #: ty
  | PApp { pfunc; args }, _ ->
      let pfunc = typed_id_infer ctx pfunc in
      let argsty, retty = Nt.destruct_arr_tp pfunc.ty in
      let args =
        List.map (fun (arg, ty) -> typed_expr_check ctx arg ty)
        @@ List.combine args argsty
      in
      let ty = Nt._type_unify [%here] retty ty in
      (PApp { pfunc; args }) #: ty
  | PAccess { container; index }, _ -> (
      let container = typed_expr_infer ctx container in
      match container.ty with
      | Nt.Ty_constructor ("map", [ ty1; ty2 ]) ->
          let index = typed_expr_check ctx index ty1 in
          let ty = Nt._type_unify [%here] ty2 ty in
          (PAccess { container; index }) #: ty
      | Nt.Ty_constructor ("set", [ ty2 ]) ->
          let index = typed_expr_check ctx index Nt.Ty_int in
          let ty = Nt._type_unify [%here] ty2 ty in
          (PAccess { container; index }) #: ty
      | _ -> _die [%here])
  | PRecord es, Nt.Ty_record tys ->
      let es =
        List.map
          (fun (name, expr) ->
            match find_in_args name tys with
            | None -> _die_with [%here] "wrong feild"
            | Some { ty; _ } -> (name, typed_expr_check ctx expr ty))
          es
      in
      let tys' = List.map (fun (name, e) -> name #: e.ty) es in
      let tys' = List.sort (compare_typed Nt.compare_nt String.compare) tys' in
      (PRecord es) #: (Nt.Ty_record tys')
  | PField { record; field }, _ -> (
      let record = typed_expr_infer ctx record in
      match record.ty with
      | Nt.Ty_record tys -> (
          match find_in_args field tys with
          | None -> _die_with [%here] "wrong feild"
          | Some { ty = ty'; _ } ->
              let ty = Nt._type_unify [%here] ty' ty in
              (PField { record; field }) #: ty)
      | _ -> _die_with [%here] "not a record type")
  | PAssign { lvalue; rvalue }, _ -> (
      let _ = Nt._type_unify [%here] ty Nt.Ty_unit in
      let lvalue = typed_expr_infer ctx lvalue in
      match lvalue.ty with
      | Nt.Ty_constructor ("ref", [ ty' ]) ->
          let rvalue = typed_expr_check ctx rvalue ty' in
          (PAssign { lvalue; rvalue }) #: Nt.Ty_unit
      | _ -> _die_with [%here] "not a ref type")
  | PDeref e, _ ->
      let e = typed_expr_check ctx e (mk_p_ref_ty ty) in
      (PDeref e) #: ty
  | PLet { lhs; rhs; body }, _ ->
      let lhs = Nt.__force_typed [%here] lhs in
      let rhs = typed_expr_check ctx rhs lhs.ty in
      let ctx' = add_to_right ctx lhs in
      let body = typed_expr_check ctx' body ty in
      (PLet { lhs; rhs; body }) #: ty
  | PSeq { rhs; body }, _ ->
      let rhs = typed_expr_check ctx rhs Nt.Ty_unit in
      let body = typed_expr_check ctx body ty in
      (PSeq { rhs; body }) #: ty
  | ForeachSet { elem; set; body }, _ ->
      let _ = Nt._type_unify [%here] ty Nt.Ty_unit in
      let set = typed_expr_infer ctx set in
      let elem_ty =
        match set.ty with
        | Nt.Ty_constructor ("set", [ ty ]) -> ty
        | _ -> _die_with [%here] "not a set type"
      in
      let elem = elem.x #: elem_ty in
      let ctx' = add_to_right ctx elem in
      let body = typed_expr_check ctx' body Nt.Ty_unit in
      (ForeachSet { elem; set; body }) #: Nt.Ty_unit
  | ForeachMap { key; map; body }, _ ->
      let _ = Nt._type_unify [%here] ty Nt.Ty_unit in
      let map = typed_expr_infer ctx map in
      let key_ty, _ =
        match map.ty with
        | Nt.Ty_constructor ("map", [ ty1; ty2 ]) -> (ty1, ty2)
        | _ -> _die_with [%here] "not a map type"
      in
      let key = key.x #: key_ty in
      let ctx' = add_to_rights ctx [ key ] in
      let body = typed_expr_check ctx' body Nt.Ty_unit in
      (ForeachMap { key; map; body }) #: Nt.Ty_unit
  | PSend { dest; event_name; payload }, _ ->
      let _ = Nt._type_unify [%here] ty Nt.Ty_unit in
      let dest = typed_expr_check ctx dest (mk_p_abstract_ty "server") in
      let event_ty =
        match get_opt ctx event_name with None -> _die [%here] | Some ty -> ty
      in
      let payload =
        typed_expr_check ctx payload (remove_server_field_record_type event_ty)
      in
      (PSend { dest; event_name; payload }) #: Nt.Ty_unit
  | PGoto name, _ ->
      let _ = Nt._type_unify [%here] ty Nt.Ty_unit in
      (PGoto name) #: Nt.Ty_unit
  | PReturn e, _ ->
      let e = typed_expr_check ctx e ty in
      let e' =
        match e.ty with
        | Nt.Ty_unit -> PSeq { rhs = e; body = mk_return_void }
        | _ -> PReturn e
      in
      e' #: ty
  | PBreak, _ ->
      let _ = Nt._type_unify [%here] ty Nt.Ty_unit in
      PBreak #: Nt.Ty_unit
  | PIf { condition; tbranch; fbranch }, _ ->
      let condition = typed_expr_check ctx condition Nt.Ty_bool in
      let tbranch = typed_expr_check ctx tbranch Nt.Ty_unit in
      let fbranch =
        match fbranch with
        | None -> None
        | Some fbranch -> Some (typed_expr_check ctx fbranch Nt.Ty_unit)
      in
      (PIf { condition; tbranch; fbranch }) #: Nt.Ty_unit
  | PPrintf (format, es), _ ->
      let _ = Nt._type_unify [%here] ty Nt.Ty_unit in
      let es = List.map (typed_expr_infer ctx) es in
      (PPrintf (format, es)) #: Nt.Ty_unit
  | _, _ -> _die_with [%here] "expr type error"

and expr_infer (ctx : t ctx) (expr : t p_expr) : (t, t p_expr) typed =
  match expr with
  | PThis ->
      let tmp = id_infer ctx "this" in
      PThis #: tmp.ty
  | PNull -> _die [%here]
  | Pid id ->
      let id = typed_id_infer ctx id in
      (Pid id) #: id.ty
  | PConst c -> (PConst c) #: (infer_constant c)
  | PApp { pfunc; args } ->
      let pfunc = typed_id_infer ctx pfunc in
      let argsty, retty = Nt.destruct_arr_tp pfunc.ty in
      let args =
        List.map (fun (arg, ty) -> typed_expr_check ctx arg ty)
        @@ List.combine args argsty
      in
      (PApp { pfunc; args }) #: retty
  | PAccess { container; index } -> (
      let container = typed_expr_infer ctx container in
      match container.ty with
      | Nt.Ty_constructor ("map", [ ty1; ty2 ]) ->
          let index = typed_expr_check ctx index ty1 in
          (PAccess { container; index }) #: ty2
      | Nt.Ty_constructor ("set", [ ty2 ]) ->
          let index = typed_expr_check ctx index Nt.Ty_int in
          (PAccess { container; index }) #: ty2
      | _ -> _die [%here])
  | PRecord es ->
      let es =
        List.map (fun (name, expr) -> (name, typed_expr_infer ctx expr)) es
      in
      let tys' = List.map (fun (name, e) -> name #: e.ty) es in
      let tys' = List.sort Stdlib.compare tys' in
      (PRecord es) #: (Nt.Ty_record tys')
  | PField { record; field } -> (
      let record = typed_expr_infer ctx record in
      match record.ty with
      | Nt.Ty_record tys -> (
          match find_in_args field tys with
          | None -> _die_with [%here] "wrong feild"
          | Some x -> (PField { record; field }) #: x.ty)
      | _ -> _die_with [%here] "not a record type")
  | PAssign { lvalue; rvalue } -> (
      let lvalue = typed_expr_infer ctx lvalue in
      match lvalue.ty with
      | Nt.Ty_constructor ("ref", [ ty' ]) ->
          let rvalue = typed_expr_check ctx rvalue ty' in
          (PAssign { lvalue; rvalue }) #: Nt.Ty_unit
      | _ -> _die_with [%here] "not a ref type")
  | PDeref e ->
      let e = typed_expr_infer ctx e in
      let ty =
        match e.ty with
        | Nt.Ty_constructor ("ref", [ ty ]) -> ty
        | _ -> _die_with [%here] "not a ref type"
      in
      (PDeref e) #: ty
  | PLet { lhs; rhs; body } ->
      let lhs = Nt.__force_typed [%here] lhs in
      let rhs = typed_expr_check ctx rhs lhs.ty in
      let ctx' = add_to_right ctx lhs in
      let body = typed_expr_infer ctx' body in
      (PLet { lhs; rhs; body }) #: body.ty
  | PSeq { rhs; body } ->
      let rhs = typed_expr_check ctx rhs Nt.Ty_unit in
      let body = typed_expr_infer ctx body in
      (PSeq { rhs; body }) #: body.ty
  | ForeachSet { elem; set; body } ->
      let set = typed_expr_infer ctx set in
      let elem_ty =
        match set.ty with
        | Nt.Ty_constructor ("set", [ ty ]) -> ty
        | _ -> _die_with [%here] "not a set type"
      in
      let elem = elem.x #: elem_ty in
      let ctx' = add_to_right ctx elem in
      let body = typed_expr_check ctx' body Nt.Ty_unit in
      (ForeachSet { elem; set; body }) #: Nt.Ty_unit
  | ForeachMap { key; map; body } ->
      let map = typed_expr_infer ctx map in
      let key_ty, _ =
        match map.ty with
        | Nt.Ty_constructor ("map", [ ty1; ty2 ]) -> (ty1, ty2)
        | _ -> _die_with [%here] "not a set type"
      in
      let key = key.x #: key_ty in
      let ctx' = add_to_rights ctx [ key ] in
      let body = typed_expr_check ctx' body Nt.Ty_unit in
      (ForeachMap { key; map; body }) #: Nt.Ty_unit
  | PSend { dest; event_name; payload } ->
      let dest = typed_expr_check ctx dest (mk_p_abstract_ty "server") in
      let event_ty =
        match get_opt ctx event_name with None -> _die [%here] | Some ty -> ty
      in
      let payload =
        typed_expr_check ctx payload (remove_server_field_record_type event_ty)
      in
      (PSend { dest; event_name; payload }) #: Nt.Ty_unit
  | PGoto name -> (PGoto name) #: Nt.Ty_unit
  | PBreak -> PBreak #: Nt.Ty_unit
  | PReturn e ->
      let e = typed_expr_infer ctx e in
      (PReturn e) #: e.ty
  | PIf _ -> typed_expr_check ctx expr #: Nt.Ty_unit Nt.Ty_unit
  | PPrintf (format, es) ->
      let es = List.map (typed_expr_infer ctx) es in
      (PPrintf (format, es)) #: Nt.Ty_unit
(* | _ -> _die_with [%here] "expr type error" *)

open Language
open P_id_typing

type t = Nt.t

let typed_op_check (ctx : t ctx) (op : (t, op) typed) (ty : t) : (t, op) typed =
  match op.x with
  | PrimOp id ->
      let id = typed_id_check ctx id #: op.ty ty in
      (PrimOp id.x) #: id.ty
  | DtConstructor id ->
      let name = dt_name_for_typectx id in
      let name = typed_id_check ctx name #: op.ty ty in
      (DtConstructor id) #: name.ty

let typed_op_infer (ctx : t ctx) (op : (t, op) typed) : (t, op) typed =
  match op.x with
  | PrimOp id ->
      let id = typed_id_infer ctx id #: op.ty in
      (PrimOp id.x) #: id.ty
  | DtConstructor id ->
      (* let _ = Printf.printf "op: %s\n" id in *)
      let name = dt_name_for_typectx id in
      let name = typed_id_infer ctx name #: op.ty in
      (DtConstructor id) #: name.ty

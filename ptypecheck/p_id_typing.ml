open Language
open Sugar

let _unify_opt loc t1 t2 = Nt._type_unify loc t1 t2

type t = Nt.t

let rec typed_id_check (ctx : t ctx) (id : (t, string) typed) (ty : t) :
    (t, string) typed =
  let ty = Nt._type_unify [%here] id.ty ty in
  id_check ctx id.x ty

and typed_id_infer (ctx : t ctx) (id : (t, string) typed) : (t, string) typed =
  match id.ty with
  | Nt.Ty_unknown -> id_infer ctx id.x
  | ty' -> id_check ctx id.x ty'

and id_infer (ctx : t ctx) (x : string) : (t, string) typed =
  match get_opt ctx x with
  | None ->
      let () = Printf.printf "connot find type of %s\n" x in
      _die [%here]
  | Some ty -> x #: ty

and id_check (ctx : t ctx) (x : string) ty =
  match get_opt ctx x with
  | None ->
      let () = Printf.printf "connot find type of %s\n" x in
      _die [%here]
  | Some ty' ->
      let ty = Nt._type_unify [%here] ty' ty in
      x #: ty

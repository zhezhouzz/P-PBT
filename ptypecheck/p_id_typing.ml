open Language
open Sugar

let _unify_opt file line t1 t2 =
  match (t1, t2) with
  | _, None -> t1
  | None, _ -> t2
  | Some t1, Some t2 -> Some (Nt._type_unify file line t1 t2)

type t = Nt.t

let rec typed_id_check (ctx : t ctx) (id : (t option, string) typed) (ty : t) :
    (t, string) typed =
  let ty =
    match id.ty with
    | None -> ty
    | Some ty' -> Nt._type_unify __FILE__ __LINE__ ty' ty
  in
  id_check ctx id.x ty

and typed_id_infer (ctx : t ctx) (id : (t option, string) typed) :
    (t, string) typed =
  match id.ty with
  | None -> id_infer ctx id.x
  | Some ty' -> id_check ctx id.x ty'

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
      let ty = Nt._type_unify __FILE__ __LINE__ ty' ty in
      x #: ty

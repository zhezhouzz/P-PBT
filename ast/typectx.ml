open Sexplib.Std
open Mtyped

type 't ctx = Typectx of ('t, string) typed list [@@deriving sexp]

open Sugar

let emp = Typectx []

let get_opt ctx name =
  match ctx with
  | Typectx l ->
      let* x = List.find_opt (fun x -> String.equal name x.x) l in
      Some x.ty

let _get_force loc ctx name =
  match get_opt ctx name with
  | None -> _die_with loc (spf "cannot find %s in the ctx" name)
  | Some x -> x

let add_to_right : 'a. 'a ctx -> ('a, string) typed -> 'a ctx =
 fun ctx { x; ty } ->
  match get_opt ctx x with
  | Some _ -> _die_with [%here] (spf "duplicate adding (%s) to ctx" x)
  | None -> ( match ctx with Typectx l -> Typectx (l @ [ { x; ty } ]))

let add_to_rights ctx l = List.fold_left add_to_right ctx l
let ctx_to_list ctx = match ctx with Typectx l -> l

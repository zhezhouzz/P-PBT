module type AST = sig
  type 'a ast [@@deriving sexp]

  val fv : 'a ast -> string
  val subst : 'a ast -> string -> 'a ast -> 'a ast
  val subst_id : 'a ast -> string -> string -> 'a ast
end

open Ast
open Zdatatype

let layout_states f s =
  List.split_by_comma f @@ List.of_seq @@ StateSet.to_seq s

let layout_qv x = spf "(%s: %s)" x.x (Nt.layout x.ty)
let layout_qvs = List.split_by " " layout_qv
let p_prim_types = [ "machine"; "any"; "string" ]

let rec is_p_prim_type = function
  | Nt.Ty_bool | Nt.Ty_int -> true
  | Nt.Ty_record l -> List.for_all (fun x -> is_p_prim_type x.ty) l
  | Nt.Ty_tuple l -> List.for_all is_p_prim_type l
  | Nt.Ty_constructor (name, [])
    when List.exists (String.equal name) p_prim_types ->
      true
  | Nt.Ty_constructor (name, [ nt ]) ->
      (String.equal "set" name || String.equal "req" name) && is_p_prim_type nt
  | Nt.Ty_constructor (name, [ nt1; nt2 ]) ->
      String.equal "map" name && is_p_prim_type nt1 && is_p_prim_type nt2
  | _ -> false

let get_absty nt =
  let rec aux = function
    | Nt.Ty_bool | Nt.Ty_int | Nt.Ty_any -> []
    | Nt.Ty_record l -> List.concat_map (fun x -> aux x.ty) l
    | Nt.Ty_tuple l -> List.concat_map aux l
    | Nt.Ty_constructor (name, [])
      when List.exists (String.equal name) p_prim_types ->
        []
    | Nt.Ty_constructor (name, []) -> [ name ]
    | Nt.Ty_constructor (_, [ nt ]) -> aux nt
    | Nt.Ty_constructor (_, [ nt1; nt2 ]) -> aux nt1 @ aux nt2
    | _ -> _die_with [%here] (Nt.layout nt)
  in
  List.slow_rm_dup String.equal (aux nt)

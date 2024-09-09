open Ast
open Common

let rec world_to_nt = function
  | WState -> Nt.Ty_int
  | WSingle { qv; world } -> Nt.Ty_tuple [ qv.ty; world_to_nt world ]
  | WMap { qv; world } -> mk_p_map_ty qv.ty (world_to_nt world)

let rec get_qvs_from_world = function
  | WState -> []
  | WSingle { qv; world; _ } -> qv :: get_qvs_from_world world
  | WMap { qv; world; _ } -> qv :: get_qvs_from_world world

(* let rec get_abstract_qvs_from_world = function *)
(*   | WState -> [] *)
(*   | WSingle { qv; world; } -> *)
(*       (qv.x #: abstract_type) :: get_abstract_qvs_from_world world *)
(*   | WMap { qv; world; } -> *)
(*       (qv.x #: abstract_type) :: get_abstract_qvs_from_world world *)

open Zdatatype

let rec layout_world = function
  | WState -> ""
  | WSingle { qv; world } ->
      spf "Exists %s.%s" (layout_qv qv) (layout_world world)
  | WMap { qv; world } -> spf "Forall %s.%s" (layout_qv qv) (layout_world world)

let mk_abstract_ctx_one ctx (e : Nt.t item) =
  match e with MAbstractType x -> StrMap.add x.x x.ty ctx | _ -> ctx

let mk_abstract_ctx es = List.fold_left mk_abstract_ctx_one StrMap.empty es

open Language

let infer_constant (c : p_const) =
  let open Nt in
  match c with
  | PUnit -> Ty_unit
  | PHalt -> Ty_unit
  | PError -> Ty_unit
  | PInt _ -> Ty_int
  | PBool _ -> Ty_bool
  | PRandomBool -> Ty_bool
  | PDefault nt -> nt
  | PStr _ -> Ty_constructor ("string", [])
(* | Tu l -> Ty_tuple (List.map infer_constant l) *)
(* | PSeqLit l -> *)
(*     let tys = List.map infer_constant l in *)
(*     let ty = *)
(*       match tys with *)
(*       | [] -> _failatwith __FILE__ __LINE__ "empty set literal is not allowed" *)
(*       | ty :: tys -> *)
(*           if List.for_all (Nt.eq ty) tys then ty *)
(*           else *)
(*             _failatwith __FILE__ __LINE__ "set contains multiple typed values" *)
(*     in *)
(*     ty_set ty *)
(* | Dt _ -> _failatwith __FILE__ __LINE__ "unimp datatype instance" *)

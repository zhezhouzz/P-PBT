open Language

let rec infer_constant (c : constant) =
  let open Nt in
  match c with
  | U -> Ty_unit
  | I _ -> Ty_int
  | B _ -> Ty_bool
  | Tu l -> Ty_tuple (List.map infer_constant l)
  | SetLiteral l ->
      let tys = List.map infer_constant l in
      let ty =
        match tys with
        | [] -> _failatwith [%here] "empty set literal is not allowed"
        | ty :: tys ->
            if List.for_all (Nt.equal_nt ty) tys then ty
            else _failatwith [%here] "set contains multiple typed values"
      in
      ty_set ty
  | Dt _ -> _failatwith [%here] "unimp datatype instance"

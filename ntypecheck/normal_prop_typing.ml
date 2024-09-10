open Language
open Normal_lit_typing
(* open Sugar *)

let bi_typed_prop_check (ctx : t ctx) (prop : t prop) : t prop =
  let rec aux ctx prop =
    match prop with
    | Lit lit -> Lit (bi_typed_lit_check ctx lit Nt.Ty_bool)
    | Implies (e1, e2) -> Implies (aux ctx e1, aux ctx e2)
    | Ite (e1, e2, e3) -> Ite (aux ctx e1, aux ctx e2, aux ctx e3)
    | Not e -> Not (aux ctx e)
    | And es -> And (List.map (aux ctx) es)
    | Or es -> Or (List.map (aux ctx) es)
    | Iff (e1, e2) -> Iff (aux ctx e1, aux ctx e2)
    | Forall { qv; body } ->
        let qv = Nt.__force_typed [%here] qv in
        Forall { qv; body = aux (add_to_right ctx qv) body }
    | Exists { qv; body } ->
        let qv = Nt.__force_typed [%here] qv in
        Exists { qv; body = aux (add_to_right ctx qv) body }
  in
  aux ctx prop

open Ast

let lift_bound_varaibles (expr : (Nt.t, Nt.t p_expr) typed) =
  let rec aux_ = function
    (* | PAssign { lvalue; _ } -> ( match lvalue.x with Pid x -> [ x ] | _ -> []) *)
    | PLet { lhs; rhs; body } ->
        let l, body = aux body in
        (lhs :: l, PSeq { rhs = mk_p_vassign (lhs, rhs); body })
    | PSeq { rhs; body } ->
        let l1, rhs = aux rhs in
        let l2, body = aux body in
        (l1 @ l2, PSeq { rhs; body })
    | ForeachMap { key; body; map } ->
        let l, body = aux body in
        (key :: l, ForeachMap { key; body; map })
    | ForeachSet { elem; body; set } ->
        let l, body = aux body in
        (elem :: l, ForeachSet { elem; body; set })
    | PIf { tbranch; fbranch; condition } -> (
        let l1, tbranch = aux tbranch in
        match fbranch with
        | None -> (l1, PIf { tbranch; fbranch; condition })
        | Some fbranch ->
            let l2, fbranch = aux fbranch in
            (l1 @ l2, PIf { tbranch; fbranch = Some fbranch; condition }))
    | _ as e -> ([], e)
  and aux e =
    let l, e' = aux_ e.x in
    (l, e' #: e.ty)
  in
  aux expr

open Zzdatatype.Datatype

let mk_p_function_decl params local_vars body =
  let vars, body = lift_bound_varaibles body in
  let local_vars =
    List.slow_rm_dup (fun a b -> String.equal a.x b.x) (local_vars @ vars)
  in
  { params; local_vars; body }

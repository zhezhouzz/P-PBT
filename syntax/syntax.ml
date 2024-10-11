include Common
include Ast

let layout_value = function
  | VVar qv -> layout_qv qv
  | VConst c -> layout_constant c

open Zdatatype
open AutomataLibrary

let is_gen env op = _get_force [%here] env.gen_ctx op

let destruct_cty_var x =
  let x' = x.x #: x.ty.nt in
  let phi = subst_prop_instance default_v (AVar x') x.ty.phi in
  (x', phi)

let se_to_cur loc se =
  let op, vs, phi = _get_sevent_fields loc se in
  { op; vs; phi }

let cur_to_se { op; vs; phi } = EffEvent { op; vs; phi }

module Plan = struct
  let layout_cur { op; vs; phi } = layout_se (EffEvent { op; vs; phi })

  let layout_elem_aux f = function
    (* | PlanObs { op; vargs } -> *)
    (*     Prop.tpEvent (spf "obs %s %s" op (List.split_by " " layout_value vargs)) *)
    | PlanAct { op; args } -> Prop.tpEvent (spf "%s(%s)" op (layout_qvs args))
    | PlanActBuffer { op; args; phi } ->
        Prop.tpEvent (spf "%s(%s)[%s]" op (layout_qvs args) (layout_prop phi))
    | PlanSe c -> layout_cur c
    | (PlanStarInv _ | PlanStar _) as r -> f r

  let layout_elem =
    layout_elem_aux (function
      | PlanStarInv cs -> SFA.layout_raw_regex (Star (MultiChar cs))
      | PlanStar r -> SFA.layout_raw_regex (Star r)
      | _ -> _die [%here])

  let omit_layout_elem =
    layout_elem_aux (function
      | PlanStarInv _ -> "□*"
      | PlanStar _ -> "r□*"
      | _ -> _die [%here])

  let layout = List.split_by ";" layout_elem
  let omit_layout = List.split_by ";" omit_layout_elem
  let layout_plan = layout
  let omit_layout_plan = layout

  let left_most_se plan =
    let rec aux (pre, rest) =
      match rest with
      | [] -> None
      | PlanSe cur :: post -> Some (pre, cur, post)
      | elem :: post -> aux (pre @ [ elem ], post)
    in
    aux ([], plan)

  let right_most_se plan =
    let* pre, cur, post = left_most_se (List.rev plan) in
    let () =
      Pp.printf "@{<green>right most@} se[%s] in %s\n" (layout_cur cur)
        (layout plan)
    in
    Some (List.rev post, cur, List.rev pre)

  let merge_triple (pre, cur, post) = pre @ [ PlanSe cur ] @ post

  let remove_star loc =
    List.filter (function
      | PlanAct _ -> true
      | PlanActBuffer _ -> _die_with loc "never"
      | PlanSe _ -> _die_with loc "still have unsolved goal"
      | PlanStar _ | PlanStarInv _ -> false)

  let value_to_lit = function VVar x -> AVar x | VConst c -> AC c

  let elem_to_cur ctx elem =
    let mk_c (op, args) =
      let vs = _get_force [%here] ctx op in
      (* let () = *)
      (*   Printf.printf "op: %s\n vs: %s\n args:%s\n" op (layout_qvs vs) *)
      (*     (List.split_by_comma layout_lit args) *)
      (* in *)
      let l = _safe_combine [%here] vs args in
      let phi =
        List.map (fun (a, b) -> lit_to_prop (mk_lit_eq_lit a.ty (AVar a) b)) l
      in
      { op; vs; phi = smart_and phi }
    in
    match elem with
    | PlanActBuffer { op; args; phi = p } ->
        let { op; vs; phi } = mk_c (op, List.map (fun x -> AVar x) args) in
        { op; vs; phi = smart_add_to p phi }
    | PlanAct { op; args } -> mk_c (op, List.map (fun x -> AVar x) args)
    | PlanSe cur -> cur
    | _ -> _die [%here]

  let elem_to_se ctx elem =
    let { op; vs; phi } = elem_to_cur ctx elem in
    EffEvent { op; vs; phi }

  let elem_to_op loc = function
    | PlanActBuffer { op; _ } | PlanAct { op; _ } | PlanSe { op; _ } -> op
    | _ -> _die loc

  let se_to_raw_regex x = SFA.(MultiChar (CharSet.singleton x))

  let elem_to_raw_regex ctx elem =
    match elem with
    | PlanAct _ | PlanSe _ | PlanActBuffer _ ->
        se_to_raw_regex (elem_to_se ctx elem)
    | PlanStar r -> Star r
    | PlanStarInv cs -> Star (MultiChar cs)

  let plan_to_raw_regex ctx plan =
    SFA.seq (List.map (elem_to_raw_regex ctx) plan)

  let smart_and_cur se1 elem =
    let () =
      Pp.printf "@{<bold>smart_and_cur:@} %s --> %s\n" (layout_cur se1)
        (layout_elem elem)
    in
    let { op = op1; vs = vs1; phi = phi_1 } = se1 in
    match elem with
    | PlanStarInv _ | PlanStar _ -> _die_with [%here] "never"
    | PlanSe se ->
        let { op = op2; phi = phi_2; _ } = se in
        if String.equal op1 op2 then
          Some (PlanSe { op = op1; vs = vs1; phi = smart_add_to phi_1 phi_2 })
        else None
    | PlanAct { op = op2; args } ->
        if String.equal op1 op2 then
          let phi_1' =
            List.fold_right
              (fun (x, y) -> subst_prop_instance x.x (AVar y))
              (_safe_combine [%here] vs1 args)
              phi_1
          in
          Some (PlanActBuffer { op = op2; args; phi = phi_1' })
        else None
    | PlanActBuffer { op = op2; args; phi = phi_2 } ->
        if String.equal op1 op2 then
          let phi_1' =
            List.fold_right
              (fun (x, y) -> subst_prop_instance x.x (AVar y))
              (_safe_combine [%here] vs1 args)
              phi_1
          in
          Some
            (PlanActBuffer { op = op2; args; phi = smart_add_to phi_1' phi_2 })
        else None

  let smart_and_cur_in_cs cs cur =
    SFA.CharSet.fold
      (fun se -> function
        | None -> smart_and_cur (se_to_cur [%here] se) cur
        | Some res -> Some res)
      cs None

  let single_insert elem trace =
    let () =
      Printf.printf "insert (%s) in %s\n" (layout_elem elem) (layout trace)
    in
    (* let se = (elem_to_se ctx) elem in *)
    let rec aux (res, pre) = function
      | [] -> res
      | PlanStar _ :: _ -> _die_with [%here] "unimp"
      | (PlanStarInv cs as x) :: rest -> (
          match smart_and_cur_in_cs cs elem with
          | Some elem' ->
              let res' = (pre @ [ x ], elem', [ x ] @ rest) in
              aux (res' :: res, pre @ [ x ]) rest
          | None ->
              aux (res, pre @ [ x ]) rest
              (* if check_regex_include (se_to_raw_regex se, MultiChar cs) then *)
              (*   let res' = (pre @ [ x ], se, [ x ] @ rest) in *)
              (*   aux (res' :: res, pre @ [ x ]) rest *)
              (* else aux (res, pre @ [ x ]) rest *))
      | ((PlanAct _ | PlanActBuffer _) as elem) :: rest ->
          aux (res, pre @ [ elem ]) rest
      (* | PlanActBuffer _ :: _ -> _die_with [%here] "never" *)
      | PlanSe cur :: rest -> (
          match smart_and_cur cur elem with
          | Some elem' ->
              aux ((pre, elem', rest) :: res, pre @ [ PlanSe cur ]) rest
          | None -> aux (res, pre @ [ PlanSe cur ]) rest)
      (* if check_regex_include (se_to_raw_regex elem', se_to_raw_regex cur') *)
      (* then aux ((pre, elem, rest) :: res, pre @ [ PlanSe cur ]) rest *)
      (* else aux (res, pre @ [ PlanSe cur ]) rest *)
    in
    let res = aux ([], []) trace in
    (* let () = *)
    (*   List.iter *)
    (*     (fun (pre, cur, post) -> *)
    (*       Printf.printf "Res: %s -- %s -- %s\n" (layout pre) (layout_elem cur) *)
    (*         (layout post)) *)
    (*     res *)
    (* in *)
    res

  let rec insert elems trace =
    (* let () = *)
    (*   Printf.printf "insert [%s] in %s\n" *)
    (*     (List.split_by_comma layout_elem elems) *)
    (*     (layout trace) *)
    (* in *)
    match elems with
    | [] -> [ trace ]
    | [ se ] ->
        List.map (fun (a, b, c) -> a @ [ b ] @ c) @@ single_insert se trace
    | se :: rest ->
        let l = single_insert se trace in
        List.concat_map
          (fun (a, b, trace) ->
            let trace' = insert rest trace in
            List.map (fun c -> a @ [ b ] @ c) trace')
          l

  let elem_drop = function
    | PlanActBuffer { op; args; _ } -> PlanAct { op; args }
    | _ as v -> v

  let eq_plan_elem a b = equal_plan_elem (elem_drop a) (elem_drop b)

  let divide_by_elem elem trace =
    let rec aux pre = function
      | [] -> _die_with [%here] "never"
      | x :: post ->
          if eq_plan_elem elem x then (pre, x, post) else aux (pre @ [ x ]) post
    in
    aux [] trace

  let parallel_interleaving l =
    let l = None :: List.map (fun x -> Some x) l in
    let l = List.permutation l in
    let rec aux pre = function
      | [] -> (pre, [])
      | None :: res -> (pre, List.filter_map (fun x -> x) res)
      | Some x :: res -> aux (pre @ [ x ]) res
    in
    List.map (aux []) l

  let msubst_lit m =
    List.fold_right (fun (x, lit) -> subst_lit_instance x lit) m

  let subst_value x value = function
    | VVar y -> if String.equal x y.x then value else VVar y
    | VConst c -> VConst c

  let lit_to_value loc = function
    | AVar x -> VVar x
    | AC c -> VConst c
    | _ -> _die loc

  let subst_elem x z = function
    | PlanActBuffer { op; args; phi } ->
        PlanActBuffer
          {
            op;
            args = List.map (subst_name_qv x z) args;
            phi = subst_prop_instance x (AVar z) phi;
          }
    | PlanAct { op; args } ->
        PlanAct { op; args = List.map (subst_name_qv x z) args }
    | PlanSe { op; vs; phi } ->
        let op, vs, phi =
          _get_sevent_fields [%here]
          @@ subst_sevent_instance x (AVar z) (EffEvent { op; vs; phi })
        in
        PlanSe { op; vs; phi }
    | PlanStarInv cs ->
        PlanStarInv (SFA.CharSet.map (subst_sevent_instance x (AVar z)) cs)
    | PlanStar r -> PlanStar (subst_raw_sregex x (AVar z) r)

  let subst_plan x z = List.map (subst_elem x z)
end

include Common
include Ast

let layout_value = function
  | VVar qv -> layout_qv qv
  | VConst c -> layout_constant c

open Zdatatype
open AutomataLibrary

module Plan = struct
  let layout_cur { op; vs; phi } = layout_se (EffEvent { op; vs; phi })

  let layout_elem_aux f = function
    | PlanObs { op; vargs } ->
        Prop.tpEvent (spf "obs %s %s" op (List.split_by " " layout_value vargs))
    | PlanGen { op; vargs } ->
        Prop.tpEvent (spf "gen %s %s" op (List.split_by " " layout_value vargs))
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
    Some (List.rev post, cur, List.rev pre)

  let merge_triple (pre, cur, post) = pre @ [ PlanSe cur ] @ post

  let remove_star loc =
    List.filter (function
      | PlanObs _ | PlanGen _ -> true
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
    | PlanObs { op; vargs } -> mk_c (op, List.map value_to_lit vargs)
    | PlanGen { op; vargs } -> mk_c (op, List.map value_to_lit vargs)
    | PlanSe cur -> cur
    | _ -> _die [%here]

  let elem_to_se ctx elem =
    let { op; vs; phi } = elem_to_cur ctx elem in
    EffEvent { op; vs; phi }

  let se_to_raw_regex x = SFA.(MultiChar (CharSet.singleton x))

  let single_insert ctx check_regex_include elem trace =
    let () =
      Printf.printf "insert (%s) in %s\n" (layout_elem elem) (layout trace)
    in
    let elem' = (elem_to_se ctx) elem in
    let rec aux (res, pre) = function
      | [] -> res
      | PlanStar _ :: _ -> _die_with [%here] "unimp"
      | (PlanStarInv cs as x) :: rest ->
          if check_regex_include (se_to_raw_regex elem', MultiChar cs) then
            let res' = (pre @ [ x ], elem, [ x ] @ rest) in
            aux (res' :: res, pre @ [ x ]) rest
          else aux (res, pre @ [ x ]) rest
      | ((PlanObs _ | PlanGen _) as elem) :: rest ->
          aux (res, pre @ [ elem ]) rest
      | PlanSe cur :: rest ->
          let cur' = (elem_to_se ctx) (PlanSe cur) in
          if check_regex_include (se_to_raw_regex elem', se_to_raw_regex cur')
          then aux ((pre, elem, rest) :: res, pre @ [ PlanSe cur ]) rest
          else aux (res, pre @ [ PlanSe cur ]) rest
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

  let rec insert ctx check elems trace =
    (* let () = *)
    (*   Printf.printf "insert [%s] in %s\n" *)
    (*     (List.split_by_comma layout_elem elems) *)
    (*     (layout trace) *)
    (* in *)
    match elems with
    | [] -> [ trace ]
    | [ elem ] ->
        List.map (fun (a, b, c) -> a @ [ b ] @ c)
        @@ single_insert ctx check elem trace
    | elem :: rest ->
        let l = single_insert ctx check elem trace in
        List.concat_map
          (fun (a, b, trace) ->
            let trace' = insert ctx check rest trace in
            List.map (fun c -> a @ [ b ] @ c) trace')
          l

  let divide_by_elem elem trace =
    let rec aux pre = function
      | [] -> _die_with [%here] "never"
      | x :: post ->
          if equal_plan_elem elem x then (pre, post) else aux (pre @ [ x ]) post
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

  let msubst f = List.fold_right (fun (x, lit) -> f x lit)

  let subst_elem x lit = function
    | PlanObs { op; vargs } ->
        let value = lit_to_value [%here] lit in
        PlanObs { op; vargs = List.map (subst_value x value) vargs }
    | PlanGen { op; vargs } ->
        let value = lit_to_value [%here] lit in
        PlanGen { op; vargs = List.map (subst_value x value) vargs }
    | PlanSe { op; vs; phi } ->
        let op, vs, phi =
          _get_sevent_fields [%here]
          @@ subst_sevent_instance x lit (EffEvent { op; vs; phi })
        in
        PlanSe { op; vs; phi }
    | PlanStarInv cs ->
        PlanStarInv (SFA.CharSet.map (subst_sevent_instance x lit) cs)
    | PlanStar r -> PlanStar (subst_raw_sregex x lit r)

  let subst_plan x lit = List.map (subst_elem x lit)
end

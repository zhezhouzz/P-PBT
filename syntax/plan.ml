open Zdatatype
open AutomataLibrary
open Common
open Ast

let layout_cur = layout_se

let layout_elem_aux f = function
  (* | PlanObs { op; vargs } -> *)
  (*     Prop.tpEvent (spf "obs %s %s" op (List.split_by " " layout_value vargs)) *)
  | PlanAct { op; args } -> tpEvent (spf "%s(%s)" op (layout_qvs args))
  | PlanActBuffer { op; args; phi } ->
      tpEvent (spf "%s(%s)[%s]" op (layout_qvs args) (layout_prop phi))
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
let omit_layout_plan = omit_layout

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

let remove_star loc plan =
  List.filter
    (function
      | PlanAct _ -> true
      | PlanActBuffer _ -> _die_with loc "never"
      | PlanSe _ -> _die_with loc "still have unsolved goal"
      | PlanStar _ | PlanStarInv _ -> false)
    plan

let value_to_lit = function VVar x -> AVar x | VConst c -> AC c

let elem_to_se ctx elem =
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
  SFA.smart_seq (List.map (elem_to_raw_regex ctx) plan)

let smart_and_se se1 elem =
  let () =
    Pp.printf "@{<bold>smart_and_se:@} %s --> %s\n" (layout_cur se1)
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
        let () = Pp.printf "op: %s\n" op1 in
        let () = Pp.printf "vs1: %s\n" (layout_qvs vs1) in
        let () = Pp.printf "args: %s\n" (layout_qvs args) in
        let phi_1' =
          List.fold_right
            (fun (x, y) -> subst_prop_instance x.x (AVar y))
            (_safe_combine [%here] vs1 args)
            phi_1
        in
        let () = Pp.printf "phi_1': %s\n" (layout_prop phi_1') in
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
        Some (PlanActBuffer { op = op2; args; phi = smart_add_to phi_1' phi_2 })
      else None

let smart_and_se_in_cs cs cur =
  SFA.CharSet.fold
    (fun se -> function None -> smart_and_se se cur | Some res -> Some res)
    cs None

let single_insert elem trace =
  let () =
    Printf.printf "insert (%s) in %s\n" (omit_layout_elem elem)
      (omit_layout trace)
  in
  (* let se = (elem_to_se ctx) elem in *)
  let rec aux (res, pre) = function
    | [] -> res
    | PlanStar _ :: _ -> _die_with [%here] "unimp"
    | (PlanStarInv cs as x) :: rest -> (
        match smart_and_se_in_cs cs elem with
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
        match smart_and_se cur elem with
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

let comple_cs cs cs' =
  let open SFA in
  let cs =
    CharSet.filter_map
      (fun se ->
        let op, vs, phi = _get_sevent_fields se in
        let phis =
          CharSet.fold
            (fun se' phis ->
              let op', _, phi' = _get_sevent_fields se' in
              if String.equal op op' then phi' :: phis else phis)
            cs' []
        in
        let phi = smart_add_to phi (Not (smart_or phis)) in
        match phi with
        | Not p when is_true p -> None
        | _ -> Some { op; vs; phi })
      cs
  in
  cs

let inter_cs cs1 cs2 =
  let open SFA in
  let cs =
    CharSet.filter_map
      (fun se ->
        let op, vs, phi = _get_sevent_fields se in
        let phis =
          CharSet.fold
            (fun se' phis ->
              let op', _, phi' = _get_sevent_fields se' in
              if String.equal op op' then phi' :: phis else phis)
            cs2 []
        in
        let phi = smart_add_to phi (smart_or phis) in
        if is_false phi then None else Some { op; vs; phi })
      cs1
  in
  cs

let rec merge_plan_elem elem1 elem2 =
  let res =
    match (elem1, elem2) with
    | PlanStar _, _ | _, PlanStar _ -> _die_with [%here] "unimp"
    | PlanStarInv cs1, PlanStarInv cs2 -> Some (PlanStarInv (inter_cs cs1 cs2))
    | PlanStarInv cs1, _ -> smart_and_se_in_cs cs1 elem2
    | _, PlanStarInv _ -> merge_plan_elem elem2 elem1
    | PlanSe cur, _ -> smart_and_se cur elem2
    | _, PlanSe _ -> merge_plan_elem elem2 elem1
    | (PlanAct _ | PlanActBuffer _), _ -> None
  in
  let () =
    _log "plan" @@ fun _ ->
    Pp.printf "@{<bold>merge-elem@} %s @{<bold>with@} %s\n"
      (omit_layout_elem elem1) (omit_layout_elem elem2)
  in
  let () =
    _log "plan" @@ fun _ ->
    Pp.printf "@{<bold>res merge-elem@} %s\n"
      (layout_option omit_layout_elem res)
  in
  res

let merge_plan l1 l2 =
  let () =
    _log "plan" @@ fun _ ->
    Pp.printf "@{<bold>>>>merge@} %s @{<bold>with@} %s\n" (omit_layout_plan l1)
      (omit_layout_plan l2)
  in
  let mk_tab l =
    let tab = Hashtbl.create (List.length l + 1) in
    let res =
      List.fold_lefti
        (fun res idx elem ->
          let () = Hashtbl.add tab idx elem in
          match elem with
          | PlanActBuffer _ | PlanAct _ | PlanSe _ -> res @ [ idx ]
          | _ -> res)
        [] l
    in
    (tab, res)
  in
  let num1, num2 = map2 List.length (l1, l2) in
  let tab1, l1 = mk_tab l1 in
  let tab2, l2 = mk_tab l2 in
  let cons_multi e l = List.map (fun l -> e :: l) l in
  let rec mk_seqence (l1, l2) =
    match (l1, l2) with
    | [], _ -> [ List.map (fun r -> (None, Some r)) l2 ]
    | _, [] -> [ List.map (fun l -> (Some l, None)) l1 ]
    | id1 :: l1, id2 :: l2 ->
        let res1 = cons_multi (Some id1, Some id2) @@ mk_seqence (l1, l2) in
        let res2 = cons_multi (Some id1, None) @@ mk_seqence (l1, id2 :: l2) in
        let res3 = cons_multi (None, Some id2) @@ mk_seqence (id1 :: l1, l2) in
        res1 @ res2 @ res3
  in
  (* let rec extend num (idx, l) = *)
  (*   if idx >= num then [] *)
  (*   else *)
  (*     match l with *)
  (*     | [] -> [ [] ] *)
  (*     | None :: l -> *)
  (*         cons_multi idx (extend num (idx, l)) *)
  (*         @ cons_multi idx (extend num (idx + 1, l)) *)
  (*         @ extend num (idx + 1, None :: l) *)
  (*     | Some idx' :: l -> if idx >= idx' then [] else extend num (idx' + 1, l) *)
  (* in *)
  (* let extend2 l = *)
  (*   let l1, l2 = List.split l in *)
  (*   let l1 = extend num1 (0, l1) in *)
  (*   let l2 = extend num2 (0, l2) in *)
  (*   let l = List.cross l1 l2 in *)
  (*   List.map (fun (x, y) -> List.combine x y) l *)
  (* in *)
  let l = mk_seqence (l1, l2) in
  let () =
    let layout_one = layout_option string_of_int in
    List.iteri
      (fun idx l ->
        Pp.printf "case[%i]: %s\n" idx
          (List.split_by_comma
             (fun (x, y) -> spf "(%s,%s)" (layout_one x) (layout_one y))
             l))
      l
  in
  (* let l = List.concat_map extend2 l in *)
  let rec fill (idx1, idx2) l =
    if idx1 >= num1 || idx2 >= num2 then []
    else if idx1 == num1 - 1 && idx2 == num2 - 1 then [ [ (idx1, idx2) ] ]
    else
      match l with
      | [] ->
          cons_multi (idx1, idx2) (fill (idx1 + 1, idx2 + 1) l)
          @ cons_multi (idx1, idx2) (fill (idx1, idx2 + 1) l)
          @ cons_multi (idx1, idx2) (fill (idx1 + 1, idx2) l)
      | (None, None) :: _ -> _die [%here]
      | (Some idx1', None) :: l' ->
          if idx1 > idx1' then []
          else if idx1 == idx1' - 1 then
            (cons_multi (idx1, idx2)
            @@ cons_multi (idx1', idx2) (fill (idx1' + 1, idx2) l'))
            @ cons_multi (idx1, idx2) (fill (idx1, idx2 + 1) l)
          else
            cons_multi (idx1, idx2) (fill (idx1 + 1, idx2 + 1) l)
            @ cons_multi (idx1, idx2) (fill (idx1, idx2 + 1) l)
            @ cons_multi (idx1, idx2) (fill (idx1 + 1, idx2) l)
      | (None, Some idx2') :: l' ->
          if idx2 >= idx2' then []
          else if idx2 == idx2' - 1 then
            (cons_multi (idx1, idx2)
            @@ cons_multi (idx1, idx2') (fill (idx1, idx2' + 1) l'))
            @ cons_multi (idx1, idx2) (fill (idx1 + 1, idx2) l)
          else
            cons_multi (idx1, idx2) (fill (idx1 + 1, idx2 + 1) l)
            @ cons_multi (idx1, idx2) (fill (idx1, idx2 + 1) l)
            @ cons_multi (idx1, idx2) (fill (idx1 + 1, idx2) l)
      | (Some idx1', Some idx2') :: l' ->
          if idx1 >= idx1' || idx2 >= idx2' then []
          else if idx1 == idx1' - 1 && idx2 == idx2' - 1 then
            cons_multi (idx1, idx2)
            @@ cons_multi (idx1', idx2') (fill (idx1' + 1, idx2' + 1) l')
          else
            cons_multi (idx1, idx2) (fill (idx1 + 1, idx2 + 1) l)
            @ cons_multi (idx1, idx2) (fill (idx1, idx2 + 1) l)
            @ cons_multi (idx1, idx2) (fill (idx1 + 1, idx2) l)
  in
  let l = List.concat_map (fill (0, 0)) l in
  let () =
    Hashtbl.iter
      (fun idx elem -> Pp.printf "tab1[%i]: %s\n" idx (omit_layout_elem elem))
      tab1
  in
  let () =
    Hashtbl.iter
      (fun idx elem -> Pp.printf "tab2[%i]: %s\n" idx (omit_layout_elem elem))
      tab2
  in
  let () =
    List.iteri
      (fun idx l ->
        Pp.printf "case[%i]: %s\n" idx
          (List.split_by_comma (fun (x, y) -> spf "(%i,%i)" x y) l))
      l
  in
  let rec f res = function
    | [] -> Some res
    | (i, j) :: l ->
        let e1 = Hashtbl.find tab1 i in
        let e2 = Hashtbl.find tab2 j in
        let* e = merge_plan_elem e1 e2 in
        f (res @ [ e ]) l
  in
  let l = List.filter_map (f []) l in
  let choose_less ll =
    let min_len =
      List.fold_left
        (fun res l ->
          let len = List.length l in
          match res with
          | None -> Some len
          | Some res -> if len < res then Some len else Some res)
        None ll
    in
    match min_len with
    | None -> ll
    | Some len -> List.filter (fun l -> len == List.length l) ll
  in
  let res = choose_less l in
  let () =
    List.iteri
      (fun idx l -> Pp.printf "@{<bold>res[%i]:@} %s\n" idx (omit_layout l))
      res
  in
  res

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

let msubst_lit m = List.fold_right (fun (x, lit) -> subst_lit_instance x lit) m

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
        _get_sevent_fields @@ subst_sevent_instance x (AVar z) { op; vs; phi }
      in
      PlanSe { op; vs; phi }
  | PlanStarInv cs ->
      PlanStarInv (SFA.CharSet.map (subst_sevent_instance x (AVar z)) cs)
  | PlanStar r -> PlanStar (subst_raw_sregex x (AVar z) r)

let subst_plan x z = List.map (subst_elem x z)

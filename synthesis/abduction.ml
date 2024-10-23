(* include Common *)
include Language
open Gamma
open Zdatatype
open Optimize

let eliminate_buffer_elem ({ bvs; bprop }, elem) =
  match elem with
  | PlanActBuffer { op; args; phi } ->
      let elem = PlanAct { op; args } in
      let bprop = smart_add_to phi bprop in
      ({ bvs; bprop }, elem)
  | _ as elem -> ({ bvs; bprop }, elem)

let eliminate_buffer_plan (gamma, plan) =
  List.fold_left
    (fun (gamma, plan) elem ->
      let gamma, elem = eliminate_buffer_elem (gamma, elem) in
      (gamma, plan @ [ elem ]))
    (gamma, []) plan

let eliminate_buffer_plan_mid (gamma, (pre, cur, post)) =
  let gamma, pre = eliminate_buffer_plan (gamma, pre) in
  let gamma, cur = eliminate_buffer_elem (gamma, cur) in
  let gamma, post = eliminate_buffer_plan (gamma, post) in
  (gamma, (pre, cur, post))

(* let eliminate_buffer ({ bvs; bprop }, plan) = *)
(*   let bprop, plan = *)
(*     List.fold_left *)
(*       (fun (prop, plan) -> function *)
(*         | PlanActBuffer { op; args; phi } -> *)
(*             let elem = PlanAct { op; args } in *)
(*             let prop = smart_add_to phi prop in *)
(*             (prop, plan @ [ elem ]) *)
(*         | _ as elem -> (prop, plan @ [ elem ])) *)
(*       (bprop, plan) plan *)
(*   in *)
(*   ({ bvs; bprop }, plan) *)

let check_valid_feature gamma lit =
  let aux lit = Gamma.check_valid gamma lit in
  (not (aux (lit_to_prop lit))) && not (aux @@ Not (lit_to_prop lit))

let check_valid_pre gamma prop = not (Gamma.check_valid gamma (Not prop))

let build_features { bvs; bprop } (abd_vars, lits) =
  let lits =
    List.filter (check_valid_feature { bvs = bvs @ abd_vars; bprop }) lits
  in
  let fvs = List.init (List.length lits) (fun _ -> [ true; false ]) in
  let fvs = List.choose_list_list fvs in
  let fvs =
    List.map
      smart_and
      #. (List.mapi (fun idx x ->
              let lit = lit_to_prop @@ List.nth lits idx in
              if x then lit else Not lit))
      fvs
  in
  let fvs = List.filter (check_valid_pre { bvs = bvs @ abd_vars; bprop }) fvs in
  fvs

let do_abduction { bvs; bprop } (checker : gamma -> bool) (abd_vars, fvs) =
  let fvs =
    List.filter
      (fun p -> checker { bvs = bvs @ abd_vars; bprop = smart_add_to bprop p })
      fvs
  in
  fvs

let mk_abd_prop fvs =
  match fvs with [] -> None | _ -> Some (simp_fvec_prop @@ smart_or fvs)

let mybuild_euf vars =
  let space = Hashtbl.create 10 in
  let () =
    List.iter
      (fun { x; ty } ->
        match Hashtbl.find_opt space ty with
        | None -> Hashtbl.add space ty [ x ]
        | Some l -> Hashtbl.replace space ty (x :: l))
      vars
  in
  let aux ty vars =
    let pairs = List.cross vars vars in
    let pairs =
      List.filter (function x, y -> compare_lit Nt.compare_nt x y > 0) pairs
    in
    let eqlits =
      List.map (fun l -> match l with x, y -> mk_lit_eq_lit ty x y) pairs
    in
    eqlits
  in
  let res =
    Hashtbl.fold
      (fun ty vars res ->
        if
          List.length vars > 1 && not (Nt.equal_nt ty (Nt.Ty_uninter "Bytes.t"))
        then aux ty vars @ res
        else res)
      space []
  in
  res

let build_fvtab env lits =
  let () =
    Pp.printf "@{<bold>lits:@} %s\n" (List.split_by_comma layout_typed_lit lits)
  in
  (* Remove boolean constants *)
  let lits =
    List.filter (function { x = AC (B _); _ } -> false | _ -> true) lits
  in
  let bvars, lits =
    List.partition
      (function
        | { x = AVar x; _ } when Nt.equal_nt x.ty Nt.Ty_bool -> true
        | _ -> false)
      lits
  in
  let additional =
    match get_opt env.tyctx ">" with
    | None -> []
    | Some _ ->
        (* if true then [] *)
        (* else *)
        let int_lits =
          List.filter (fun lit -> Nt.equal_nt Nt.Ty_int lit.ty) lits
        in
        let () =
          Pp.printf "@{<bold>int lits:@} %s\n"
            (List.split_by_comma layout_typed_lit int_lits)
        in
        let pairs = List.combination_l int_lits 2 in
        let ltlits =
          let lt = ">" #: Nt.(construct_arr_tp ([ Ty_int; Ty_int ], Ty_bool)) in
          List.map
            (fun l ->
              match l with
              | [ x; y ] -> AAppOp (lt, [ x; y ])
              | _ -> _die [%here])
            pairs
        in
        let () =
          Pp.printf "@{<bold>ltlits:@} %s\n"
            (List.split_by_comma layout_lit ltlits)
        in
        ltlits
  in
  let bvars = List.map _get_x bvars in
  let res = bvars @ mybuild_euf lits @ additional in
  let () =
    Pp.printf "@{<bold>build_fvtab:@} %s\n" (List.split_by_comma layout_lit res)
  in
  res

let mk_raw_all env =
  let l =
    List.map (fun x -> { op = x.x; vs = x.ty; phi = mk_true })
    @@ ctx_to_list env.event_tyctx
  in
  if List.length l == 0 then _die [%here] else SFA.CharSet.of_list l

(* let check_regex_nonempty env checker (qvs, r) = *)
(*   (\* let all = mk_raw_all env in *\) *)
(*   (\* let () = Pp.printf "@{<bold>r@}: %s\n" (layout_symbolic_regex_precise r) in *\) *)
(*   let goals = *)
(*     Desymbolic.desymbolic_reg OriginalFA env.event_tyctx checker (qvs, r) *)
(*   in *)
(*   List.for_all *)
(*     (fun (_, _, reg) -> *)
(*       let open DesymFA in *)
(*       let dfa = compile_regex_to_dfa reg in *)
(*       let dfa = minimize dfa in *)
(*       (\* let () = Printf.printf "dfa:\n%s\n" (layout_dfa dfa) in *\) *)
(*       StateSet.is_empty dfa.finals) *)
(*     goals *)

let check_regex_nonempty env { bprop; _ } r =
  let _, r' =
    Rawdesym.desymbolic_symbolic_rewregex env.tyctx env.event_tyctx (bprop, r)
  in
  not @@ DesymFA.emptiness r'

let abduction_automata env { bvs; bprop } (a : SFA.raw_regex) abd_vars =
  let lits = Rawdesym.mk_global_ftab env.tyctx (bvs @ abd_vars, bprop, a) in
  let lits =
    List.filter
      (fun lit ->
        not
          (List.is_empty
          @@ List.interset String.equal (fv_lit_id lit)
               (List.map _get_x abd_vars)))
      (build_fvtab env @@ List.map (fun l -> l #: (lit_to_nt l)) lits)
  in
  let fvs = build_features { bvs; bprop } (abd_vars, lits) in
  let () =
    Pp.printf "@{<bold>abduction_automata fvs:@}: %i\n" (List.length fvs)
  in
  (* let checker gamma (_, prop) = check_valid gamma prop in *)
  let fvs =
    do_abduction { bvs; bprop }
      (fun gamma ->
        let () = Pp.printf "@{<bold>gamma@}: %s\n" (Gamma.layout gamma) in
        let res = check_regex_nonempty env gamma a in
        let () =
          Pp.printf "@{<bold>@{<yellow>abduction_automata@}@}: %b\n" res
        in
        res)
      (abd_vars, fvs)
  in
  (* let () = if List.length fvs > 1 then _die [%here] in *)
  fvs

(* let abduction_automata env { bvs; bprop } (a : SFA.raw_regex) abd_vars = *)
(*   let open SFA in *)
(*   let { global_lits; local_lits } = gather_regex @@ raw_regex_to_regex a in *)
(*   let cur_lits = *)
(*     global_lits @ List.concat @@ List.map snd @@ StrMap.to_value_list local_lits *)
(*   in *)
(*   let cs = *)
(*     get_consts (smart_add_to bprop @@ And (List.map lit_to_prop cur_lits)) *)
(*   in *)
(*   let lits = *)
(*     List.map (fun c -> AC c) cs @ List.map (fun x -> AVar x) @@ bvs @ abd_vars *)
(*   in *)
(*   let lits = *)
(*     List.filter *)
(*       (fun lit -> *)
(*         not *)
(*           (List.is_empty *)
(*           @@ List.interset String.equal (fv_lit_id lit) *)
(*                (List.map _get_x abd_vars))) *)
(*       (build_fvtab env @@ List.map (fun l -> l #: (lit_to_nt l)) lits) *)
(*   in *)
(*   let fvs = build_features { bvs; bprop } (abd_vars, lits) in *)
(*   let () = *)
(*     Pp.printf "@{<bold>abduction_automata fvs:@}: %i\n" (List.length fvs) *)
(*   in *)
(*   (\* let checker gamma (_, prop) = check_valid gamma prop in *\) *)
(*   let fvs = *)
(*     do_abduction { bvs; bprop } *)
(*       (fun gamma -> *)
(*         let () = Pp.printf "@{<bold>gamma@}: %s\n" (Gamma.layout gamma) in *)
(*         let res = check_regex_nonempty env gamma a in *)
(*         let () = *)
(*           Pp.printf "@{<bold>@{<yellow>abduction_automata@}@}: %b\n" res *)
(*         in *)
(*         res) *)
(*       (abd_vars, fvs) *)
(*   in *)
(*   (\* let () = if List.length fvs > 1 then _die [%here] in *\) *)
(*   fvs *)

let abduction_plan env gamma plan abd_vars =
  let a = Plan.plan_to_raw_regex env.event_tyctx plan in
  abduction_automata env gamma a abd_vars

let abduction_mid_goal env gamma (plan1, elem, plan2) abd_vars =
  let plan = plan1 @ [ elem ] @ plan2 in
  let fvs = abduction_plan env gamma plan abd_vars in
  match fvs with
  | [] ->
      let () =
        if String.equal (Plan.elem_to_se env.event_tyctx elem).op "putReq" then
          _die [%here]
      in
      None
  | _ ->
      Some
        {
          bvs = gamma.bvs @ abd_vars;
          bprop = smart_add_to (smart_or fvs) gamma.bprop;
        }

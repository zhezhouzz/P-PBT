open Language
open Common
open Zdatatype
open Optimize

let backtrack f l =
  List.fold_left
    (fun res x ->
      match res with
      | Some _ -> res
      | None ->
          (* let () = _die_with [%here] "backtrack fail" in *)
          f x)
    None l

let raw_regex_to_trace = function Seq l -> l | _ -> _die [%here]
let se_to_raw_regex se = MultiChar (SFA.CharSet.singleton se)

let raw_regex_to_cs r =
  let rec aux r =
    match r with
    | MultiChar cs -> Some cs
    | Comple (cs, r) ->
        let* cs' = aux r in
        Some (Plan.comple_cs cs cs')
    | Inters (r1, r2) ->
        let* cs1 = aux r1 in
        let* cs2 = aux r2 in
        Some (Plan.inter_cs cs1 cs2)
    | _ -> None
  in
  aux r

let raw_regex_to_plan_elem r =
  let open SFA in
  let r = unify_raw_regex r in
  let r = simp_fvec_raw_regex r in
  match r with
  | MultiChar cs ->
      let se = charset_to_se [%here] cs in
      let op, vs, phi = _get_sevent_fields se in
      PlanSe { op; vs; phi }
  | Star r -> (
      match raw_regex_to_cs r with
      | Some cs -> PlanStarInv cs
      | None ->
          let () =
            Printf.printf "Not a star:\n %s\n"
              (show_raw_regex (fun _ _ -> ()) r)
          in
          _die [%here])
  | Seq _ | Empty | Eps | Alt _ | Inters _ | Comple _ -> _die [%here]

open Gamma

let raw_regex_to_plan =
  let rec aux r =
    match r with
    | Empty -> _die [%here]
    | Eps -> []
    | MultiChar _ | Star _ -> [ raw_regex_to_plan_elem r ]
    | Alt _ | Inters _ | Comple _ ->
        let () = Printf.printf "%s\n" (SFA.layout_raw_regex r) in
        _die [%here]
    | Seq l -> List.concat_map aux l
  in
  aux

let normalize_desym_regex2 (rawreg : DesymFA.raw_regex) =
  let open DesymFA in
  (* let () = Pp.printf "@{<bold>start@}: %s\n" (layout_raw_regex rawreg) in *)
  let rec aux rawreg =
    match rawreg with
    | Empty | Eps | MultiChar _ -> rawreg
    | Alt (r1, r2) -> smart_alt (aux r1) (aux r2)
    | Comple (cs1, Comple (cs2, r)) ->
        let () =
          Pp.printf "@{<bold>double comp@}: %s\n" (layout_raw_regex rawreg)
        in
        let cs1 = CharSet.filter (fun c -> not (CharSet.mem c cs2)) cs1 in
        if CharSet.is_empty cs1 then aux r else Alt (Star (MultiChar cs1), aux r)
    | Comple (cs, r) -> (
        match aux r with
        | Star (MultiChar cs') ->
            let () =
              Pp.printf "@{<bold>opt comple1@}: %s\n" (layout_raw_regex rawreg)
            in
            let cs'' = CharSet.filter (fun c -> not (CharSet.mem c cs')) cs in
            Star (MultiChar cs'')
        | _ as r ->
            let () =
              Pp.printf "@{<bold>opt comple fail@}: %s\n" (layout_raw_regex r)
            in
            do_normalize_desym_regex rawreg)
    | Inters _ ->
        let () =
          Pp.printf "@{<bold>opt inters@}: %s\n" (layout_raw_regex rawreg)
        in
        do_normalize_desym_regex rawreg
    | Seq l -> smart_seq (List.map aux l)
    | Star r -> Star (do_normalize_desym_regex r)
  in
  aux rawreg

let normalize_gamma env { bvs; bprop } r =
  let ftab = Rawdesym.mk_global_ftab env.tyctx (bvs, bprop, r) in
  let () = _assert [%here] "assume start from true" (is_true bprop) in
  let fvecs =
    List.of_seq @@ Rawdesym.BlistSet.to_seq @@ Rawdesym.mk_fvec_from_ftab ftab
  in
  let _, lit2int = Rawdesym.mk_li_map ftab in
  let props = List.map (fun l -> Rawdesym.blist_to_prop l lit2int) fvecs in
  let props =
    List.filter (fun p -> Prover.check_sat_bool (smart_exists bvs p)) props
  in
  List.map (fun bprop -> { bvs; bprop }) props

let normalize_goal_aux env (gamma, reg) =
  let () =
    Pp.printf "\n@{<bold>Before Normalize:@}\n%s\n" (SFA.layout_raw_regex reg)
  in
  let desym_ctx, reg =
    Rawdesym.desymbolic_symbolic_rewregex env.tyctx env.event_tyctx
      (gamma.bprop, reg)
  in
  let reg = Rawdesym.normalize_desym_regex reg in
  let open DesymFA in
  let () = Printf.printf "reg: %s\n" (layout_raw_regex reg) in
  if emptiness reg then []
  else
    let unf = raw_regex_to_union_normal_form unify_charset_by_op reg in
    let unf = List.map (List.map (Rawdesym.resym_regex desym_ctx)) unf in
    let unf =
      List.map (fun l -> (gamma, List.map raw_regex_to_plan_elem l)) unf
    in
    unf

let normalize_goal env (gamma, reg) =
  let gammas = normalize_gamma env gamma reg in
  let res =
    List.concat_map (fun gamma -> normalize_goal_aux env (gamma, reg)) gammas
  in
  (* let () = Pp.printf "@{<bold>Goals:\n@}" in *)
  (* let () = List.iter simp_print_mid_judgement res in *)
  (* let () = _die [%here] in *)
  res

let cur_to_obs { op; vs; phi } =
  let args = List.map (fun x -> (Rename.unique x.x) #: x.ty) vs in
  let phi =
    List.fold_right
      (fun (x, y) p -> subst_prop_instance x.x (AVar y) p)
      (_safe_combine [%here] vs args)
      phi
  in
  (args, phi, PlanAct { args; op })
(* (args, phi, PlanActBuffer { args; op; phi }) *)

let preserve_goals = ref SFA.CharSet.empty

let print_preserve_goals () =
  Pp.printf "@{<bold>preserve_goals:@}\n";
  SFA.CharSet.iter
    (fun c -> Pp.printf "Preserved Goal: %s\n" (layout_se c))
    !preserve_goals

let mk_preserve_subgoal plan =
  preserve_goals :=
    SFA.CharSet.of_list
    @@ List.filter_map (function PlanSe cur -> Some cur | _ -> None) plan

let remove_preserve_subgoal elem =
  preserve_goals :=
    SFA.CharSet.remove
      (match elem with PlanSe cur -> cur | _ -> _die [%here])
      !preserve_goals

let in_preserve_subgoal elem =
  SFA.CharSet.mem
    (match elem with PlanSe cur -> cur | _ -> _die [%here])
    !preserve_goals

(* let counter = ref 0 *)

let left_most_se plan =
  let rec aux (pre, rest) =
    match rest with
    | [] -> None
    | PlanSe cur :: post -> Some (pre, cur, post)
    | elem :: post -> aux (pre @ [ elem ], post)
  in
  aux ([], plan)

let right_most_se plan =
  let open Plan in
  let* pre, cur, post = left_most_se (List.rev plan) in
  (* let () = if !counter >= 2 then _die [%here] in *)
  Some (List.rev post, cur, List.rev pre)

let rec deductive_synthesis_reg env goal : plan sgoal option =
  let goals = normalize_goal env goal in
  let res = List.filter_map (deductive_synthesis_trace env) goals in
  match res with [] -> None | g :: _ -> Some g

and deductive_synthesis_trace env goal : plan sgoal option =
  (* let goal = map_goal raw_regex_to_trace goal in *)
  let () = simp_print_syn_judgement goal in
  let rec handle ((gamma, reg) as goal) =
    (* let () = if !counter >= 2 then _die [%here] in *)
    match right_most_se reg with
    | None -> Some goal
    | Some (pre, cur, post) ->
        let () = Pp.printf "@{<green>right most@} %s\n" (Plan.layout_cur cur) in
        (* let args, gprop', obs_elem = cur_to_obs cur in *)
        (* let subgamma = *)
        (*   { bvs = gamma.bvs @ args; bprop = smart_add_to gprop' gamma.bprop } *)
        (* in *)
        let () = remove_preserve_subgoal (PlanSe cur) in
        let subgoal = (gamma, (pre, PlanSe cur, post)) in
        (* let _, subgoal = optimize_back_goal subgoal args in *)
        let* goal = backward env subgoal in
        let () = Printf.printf "next step\n" in
        let () = simp_print_syn_judgement goal in
        (* let () = counter := !counter + 1 in *)
        handle goal
  in
  let () = mk_preserve_subgoal (snd goal) in
  let* gamma, reg = handle goal in
  let gamma, reg = Abduction.eliminate_buffer_plan (gamma, reg) in
  Some (gamma, Plan.remove_star [%here] reg)

and forward env ((gamma, (pre, elem, post)) as goal) =
  let () = simp_print_forward_judgement goal in
  let init_elem = ref (Some elem) in
  let counter = ref 0 in
  let rec aux ({ bvs; bprop } as gamma) solved rest =
    let () = counter := !counter + 1 in
    let () = simp_print_gamma_judgement { bvs; bprop } in
    let () = Printf.printf "forward solved: %s\n" (Plan.omit_layout solved) in
    let () = Printf.printf "forward rest: %s\n" (Plan.omit_layout rest) in
    let () =
      Printf.printf "init_elem\" %s\n"
        (match !init_elem with
        | None -> "none"
        | Some e -> Plan.omit_layout_elem e)
    in
    match rest with
    | [] -> Some ({ bvs; bprop }, solved)
    | (PlanSe cur as elem) :: rest ->
        let () = print_preserve_goals () in
        if not (in_preserve_subgoal elem) then
          let op = cur.op in
          (* let args, phi, elem = cur_to_obs cur in *)
          let () = Printf.printf "do: %s\n" (Plan.layout_elem elem) in
          let hafts =
            haft_to_triple @@ fresh_haft
            @@ _get_force [%here] env.event_rtyctx op
          in
          let handle haft =
            let gargs, (args, retrty) = destruct_haft [%here] haft in
            let history, _, p = destruct_hap [%here] retrty in
            (* NOTE: history should be well-formed. *)
            let history_plan = raw_regex_to_plan history in
            let dep_elem =
              let args = List.map (fun x -> x.x #: x.ty.nt) args in
              PlanAct { op; args }
            in
            let () = if !counter == 1 then init_elem := Some dep_elem in
            let dep_elem =
              match Plan.smart_and_se cur dep_elem with
              | None -> _die_with [%here] "never"
              | Some x -> x
            in
            let args, arg_phis = List.split @@ List.map destruct_cty_var args in
            let gamma = { bvs; bprop = smart_and (bprop :: arg_phis) } in
            let p = List.map (fun se -> PlanSe se) p in
            let posts = Plan.insert p rest in
            let pres = Plan.merge_plan solved history_plan in
            let goals =
              List.map (fun (pre, post) ->
                  let goal =
                    Abduction.eliminate_buffer_plan_mid
                      (gamma, (pre, dep_elem, post))
                  in
                  (goal, gargs @ args))
              @@ List.cross pres posts
            in
            goals
          in
          let goals = List.concat_map handle hafts in
          let () =
            Pp.printfBold "len(subgoals) " @@ spf "%i\n" (List.length goals)
          in
          let () =
            List.iter
              (fun (goal, vars) ->
                let () =
                  Pp.printfBold "vars:" @@ spf "%s\n" (layout_qvs vars)
                in
                simp_print_goal_judgement goal)
              goals
          in
          (* let () = if String.equal op "commit" then _die [%here] in *)
          (* let () = if String.equal op "eShardUpdateKeyReq" then _die [%here] in *)
          let abd_and_backtract ((gamma, mid_plan), args) =
            let () =
              Pp.printf "@{<bold>Before Abduction [%s]@}:\n" (layout_qvs args);
              simp_print_goal_judgement (gamma, mid_plan)
            in
            let args', (gamma, mid_plan) =
              optimize_back_goal_also_record (gamma, mid_plan) args init_elem
            in
            let () =
              Pp.printf "@{<bold>After Opt@}: (%s)\n" (layout_qvs args');
              simp_print_goal_judgement (gamma, mid_plan)
            in
            let* gamma' =
              Abduction.abduction_mid_goal env gamma mid_plan args'
            in
            let () =
              Pp.printf "@{<bold>After Abduction@}:\n";
              simp_print_goal_judgement (gamma', mid_plan)
            in
            let pre, mid, post = mid_plan in
            aux gamma' (pre @ [ mid ]) post
          in
          backtrack abd_and_backtract goals
        else aux gamma (solved @ [ elem ]) rest
    | elem :: rest -> aux { bvs; bprop } (solved @ [ elem ]) rest
  in
  let goal = aux gamma pre (elem :: post) in
  match !init_elem with
  | None -> Some (gamma, (pre, elem, post))
  | Some elem ->
      let* goal = goal in
      let gamma, plan = Abduction.eliminate_buffer_plan goal in
      let () =
        Pp.printf "find %s in\n%s\n" (Plan.layout_elem elem)
          (Plan.omit_layout plan)
      in
      let pre, elem, post = Plan.divide_by_elem elem plan in
      (* let clear *)
      Some (gamma, (pre, elem, post))

and backward env (goal : (plan * plan_elem * plan) sgoal) : plan sgoal option =
  let* goal = forward env goal in
  let () = simp_print_back_judgement goal in
  let gamma, (pre, elem, post) = goal in
  let op = Plan.elem_to_op [%here] elem in
  (* let () = if String.equal op "commit" then _die [%here] in *)
  if is_gen env op then
    (* let () = if String.equal op "writeReq" then _die [%here] in *)
    Some (gamma, pre @ [ elem ] @ post)
  else
    let handle (se, haft) =
      let () =
        Pp.printf "@{<bold>use rty@}\n@{<red>se@}: %s\n@{<red>haft@}: %s\n"
          (layout_se se)
          (layout_haft SFA.layout_raw_regex haft)
      in
      let elem =
        match Plan.smart_and_se se elem with
        | Some x -> x
        | None -> _die [%here]
      in
      let gargs, (args, retrty) = destruct_haft [%here] haft in
      let history, dep_se, p = destruct_hap [%here] retrty in
      let () = Pp.printf "@{<bold>dep_se:@} %s\n" (layout_se dep_se) in
      (* NOTE: history should be well-formed. *)
      let history_plan = raw_regex_to_plan history in
      let () =
        Pp.printf "@{<bold>history_plan:@} %s\n" (Plan.omit_layout history_plan)
      in
      let dep_elem =
        (* NOTE: the payload should just conj of eq *)
        let op, _, _ = _get_sevent_fields dep_se in
        let args = List.map (fun x -> x.x #: x.ty.nt) args in
        PlanAct { op; args }
      in
      (* let () = Printf.printf "dep_elem: %s\n" (Plan.layout_elem dep_elem) in *)
      let args, arg_phis = List.split @@ List.map destruct_cty_var args in
      let gamma =
        Gamma.simplify
          { gamma with bprop = smart_and (gamma.bprop :: arg_phis) }
      in
      let p = List.map (fun se -> PlanSe se) p in
      let fs = Plan.parallel_interleaving p in
      let () =
        List.iter
          (fun (p1, p2) ->
            Pp.printf "@{<bold>fs@}: %s -- %s\n" (Plan.layout p1)
              (Plan.layout p2))
          fs
      in
      let goals =
        List.concat_map
          (fun (f11, f12) ->
            let () = Pp.printfBold "init post:" "\n" in
            let () = Pp.printf "%s\n" @@ Plan.omit_layout_plan post in
            let posts = Plan.insert f12 post in
            (* let old_cur =  { op; vs; phi = smart_add_to phi' phi } in *)
            let f11' = dep_elem :: f11 in
            let pres =
              List.map (Plan.divide_by_elem dep_elem) @@ Plan.insert f11' pre
            in
            let () = Pp.printfBold "pres:" "\n" in
            let () = List.iter simp_print_mid_judgement pres in
            let pres =
              List.concat_map
                (fun (pre1, dep_elem', pre2) ->
                  let pre1s = Plan.merge_plan history_plan pre1 in
                  List.map (fun pre1 -> (pre1, dep_elem', pre2)) pre1s)
                pres
            in
            let () = Pp.printfBold "pres after merge:" "\n" in
            let () =
              List.iter
                (fun (a, b, c) ->
                  let lena, lenc = map2 List.length (a, c) in
                  Pp.printf "[%i][1][%i]\n" lena lenc;
                  simp_print_mid_judgement (a, b, c))
                pres
            in
            let () = Pp.printfBold "posts:" "\n" in
            let () =
              List.iter
                (fun p -> Pp.printf "%s\n" @@ Plan.omit_layout_plan p)
                posts
            in
            let goals =
              List.map (fun ((pre1, dep_elem', pre2), post) ->
                  (gamma, (pre1, dep_elem', pre2 @ [ elem ] @ post)))
              @@ List.cross pres posts
            in
            goals)
          fs
      in
      let goals = List.map Abduction.eliminate_buffer_plan_mid goals in
      let () =
        Pp.printfBold "len(subgoals) " @@ spf "%i\n" (List.length goals)
      in
      let () = Pp.printfBold "gargs:" @@ spf "%s\n" (layout_qvs gargs) in
      let () = Pp.printfBold "args:" @@ spf "%s\n" (layout_qvs args) in
      let () = List.iter simp_print_goal_judgement goals in
      let goals =
        List.map (fun (gamma, reg) -> (gargs @ args, gamma, reg)) goals
      in
      goals
    in
    let rules = select_rule_by_future env op in
    let () =
      List.iteri
        (fun i (se, haft) ->
          let () =
            Pp.printf
              "@{<bold>available rty %i@}\n@{<red>se@}: %s\n@{<red>haft@}: %s\n"
              i (layout_se se)
              (layout_haft SFA.layout_raw_regex haft)
          in
          ())
        rules
    in
    let goals = List.concat_map handle rules in
    let abd_and_backtract (args, gamma, mid_plan) =
      let () =
        Pp.printf "@{<bold>Before Abduction [%s]@}:\n" (layout_qvs args);
        simp_print_goal_judgement (gamma, mid_plan)
      in
      let args', (gamma, mid_plan) =
        optimize_back_goal (gamma, mid_plan) args
      in
      let () =
        Pp.printf "@{<bold>After Opt@}: (%s)\n" (layout_qvs args');
        simp_print_goal_judgement (gamma, mid_plan)
      in
      let* gamma' = Abduction.abduction_mid_goal env gamma mid_plan args' in
      let () =
        Pp.printf "@{<bold>After Abduction@}:\n";
        simp_print_goal_judgement (gamma', mid_plan)
      in
      backward env (gamma', mid_plan)
    in
    let goals =
      List.sort
        (fun (_, _, (a1, b1, c1)) (_, _, (a2, b2, c2)) ->
          compare
            (List.length (a1 @ [ b1 ] @ c1))
            (List.length (a2 @ [ b2 ] @ c2)))
        goals
    in
    (* let goals = List.map optimize_back_goal goals in *)
    backtrack abd_and_backtract (List.rev goals)
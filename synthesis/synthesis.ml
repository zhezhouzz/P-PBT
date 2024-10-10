open Language

type sregex = Nt.t sevent raw_regex

type 'a sgoal = {
  qvs : (Nt.t, string) typed list;
  global_prop : Nt.t prop;
  reg : 'a;
}

let map_goal f { qvs; global_prop; reg } = { qvs; global_prop; reg = f reg }

open Zdatatype

let mk_synthesis_goal (env : syn_env) =
  let qvs, prop =
    match env.goal with
    | None -> _die_with [%here] "no goal"
    | Some { qvs; prop } -> (qvs, prop)
  in
  (* let rctx = *)
  (*   add_to_rights emp *)
  (*     (List.map (fun x -> x.x #: { nt = x.ty; phi = mk_true }) qvs) *)
  (* in *)
  let reg = smart_negate prop in
  let op_names = List.map _get_x (ctx_to_list env.event_tyctx) in
  let reg =
    desugar env.event_tyctx (SyntaxSugar (CtxOp { op_names; body = reg }))
  in
  let reg = delimit_context delimit_cotexnt_se reg in
  let () = Printf.printf "Original Reg: %s\n" (layout_symbolic_regex reg) in
  let goal = { qvs; global_prop = mk_true; reg = SFA.regex_to_raw reg } in
  goal
(* (rctx, reg) *)

let layout_planing_judgement goal f =
  let ctx_str =
    spf "%s | %s" (layout_qvs goal.qvs) (layout_prop goal.global_prop)
  in
  Printf.printf "%s|- %s\n\n" ctx_str (f goal.reg)

let layout_syn_reg_judgement goal =
  layout_planing_judgement goal SFA.layout_raw_regex

let layout_syn_plan_judgement goal = layout_planing_judgement goal Plan.layout

let layout_syn_back_judgement goal =
  let open Plan in
  layout_planing_judgement goal (fun (pre, cur, post) ->
      spf "back [%s] %s [%s]" (omit_layout pre) (layout_elem cur)
        (omit_layout post))

(* let layout_syn_tmp_judgement goal = *)
(*   (\* let open SFA in *\) *)
(*   layout_planing_judgement goal (fun (pre, se, post) -> *)
(*       spf "tmp [%s] %s [%s]" *)
(*         (SFA.omit_layout_symbolic_trace pre) *)
(*         la *)
(*         (SFA.omit_layout_symbolic_trace post)) *)

(* let layout_planing_judgement goal = *)
(*   let ctx_str = *)
(*     spf "%s | %s" (layout_qvs goal.qvs) (layout_prop goal.global_prop) *)
(*   in *)
(*   let fa = DesymFA.compile_regex_to_dfa goal.reg in *)
(*   let () = Printf.printf "%s\n" (DesymFA.layout_dfa fa) in *)
(*   let res = DesymFA.dfa_to_reg fa in *)
(*   let res = to_union_normal_form res in *)
(*   let () = Printf.printf "%s\n" (layout_union_normal_form res) in *)
(*   (\* let reg_str = DesymFA.layout_dfa fa in *\) *)
(*   (\* let reg_str = DesymFA.layout_raw_regex res in *\) *)
(*   spf "%s|- %s" ctx_str ".." *)

let build_fvtab lits =
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
  let bvars = List.map _get_x bvars in
  bvars @ build_euf lits

[@@@warning "-27"]
[@@@warning "-26"]

let backtrack f l =
  List.fold_left
    (fun res x -> match res with Some _ -> res | None -> f x)
    None l

let raw_regex_to_trace = function Seq l -> l | _ -> _die [%here]

let charset_to_se loc s =
  let open SFA in
  match List.of_seq @@ CharSet.to_seq s with [ x ] -> x | _ -> _die loc

let se_to_raw_regex se = MultiChar (SFA.CharSet.singleton se)

let raw_regex_to_plan_elem r =
  let open SFA in
  let r = unify_raw_regex r in
  match r with
  | MultiChar cs ->
      let se = charset_to_se [%here] cs in
      let op, vs, phi = _get_sevent_fields [%here] se in
      PlanSe { op; vs; phi }
  | Star (MultiChar cs) -> PlanStarInv cs
  | Star r ->
      let () =
        Printf.printf "Not a star:\n %s\n" (show_raw_regex (fun _ _ -> ()) r)
      in
      _die [%here]
  | Seq _ | Empty | Eps | Alt _ | Inters _ | Comple _ -> _die [%here]

let normalize_goal env { qvs; global_prop = old_global_prop; reg } =
  let checker (_, prop) =
    let () = Printf.printf "check: %s\n" (layout_prop prop) in
    Prover.check_sat_bool (And [ old_global_prop; prop ])
  in
  let goals =
    Desymbolic.desymbolic_reg OriginalFA env.event_tyctx checker
      (qvs, SFA.raw_regex_to_regex reg)
  in
  let open DesymFA in
  let goals =
    List.concat_map
      (fun (global_prop, backward_maping, reg) ->
        (* let () = *)
        (*   Printf.printf "reg: %s\n" (layout_raw_regex (regex_to_raw reg)) *)
        (* in *)
        let reg = normalize_desym_regex @@ regex_to_raw reg in
        if is_empty_raw_regex reg then []
        else
          let unf =
            DesymFA.raw_regex_to_union_normal_form unify_charset_by_op reg
          in
          let unf = List.map (List.map (raw_reg_map backward_maping)) unf in
          let unf =
            List.map
              (fun l ->
                { qvs; global_prop; reg = List.map raw_regex_to_plan_elem l })
              unf
          in
          unf)
      goals
  in
  goals

let mk_cur loc r =
  let open SFA in
  match r with
  | MultiChar cur -> (
      let l = List.of_seq @@ CharSet.to_seq cur in
      match l with
      | [ EffEvent { op; vs; phi } ] -> { op; vs; phi }
      | _ -> _die loc)
  | _ -> _die loc

let rec filter_rule_by_future op = function
  | RtyHAParallel { parallel; adding_se; history } -> (
      (* HACK: assume each op only has one sevent. *)
      let ses, parallel' =
        List.partition
          (fun se -> String.equal op (_get_sevent_name [%here] se))
          parallel
      in
      match ses with
      | [] -> None
      | [ se ] ->
          let () =
            Printf.printf "parallel %s --> %s\n"
              (List.split_by_comma layout_se parallel)
              (List.split_by_comma layout_se parallel')
          in
          Some (se, RtyHAParallel { parallel = parallel'; adding_se; history })
      | _ -> _die_with [%here] "assume each op only has one sevent")
  | RtyArr { arg; argcty; retrty } ->
      let* se, retrty = filter_rule_by_future op retrty in
      Some (se, RtyArr { arg; argcty; retrty })
  | _ -> _die [%here]

let select_rule_by_future env op =
  List.concat_map
    (fun x ->
      let l = haft_to_triple x.ty in
      let l = List.filter_map (filter_rule_by_future op) l in
      l)
    (List.map (fun x -> x.x #: (fresh_haft x.ty))
    @@ ctx_to_list env.event_rtyctx)

let select_rule_by_adding env op =
  match get_opt env.event_rtyctx op with
  | None -> _die [%here]
  | Some haft -> haft_to_triple @@ fresh_haft haft

let se_to_cur loc se =
  let op, vs, phi = _get_sevent_fields loc se in
  { op; vs; phi }

let abduction_prop (qvs, local_vs, gprop, prop) =
  let () = Printf.printf "qvs: %s\n" (layout_qvs qvs) in
  let () = Printf.printf "gprop: %s\n" (layout_prop gprop) in
  let () = Printf.printf "qvs: %s\n" (layout_qvs local_vs) in
  let () = Printf.printf "prop: %s\n" (layout_prop prop) in
  let check_valid_feature lit =
    let aux prop =
      Prover.check_valid (smart_forall qvs @@ smart_implies gprop prop)
    in
    (not (aux @@ lit_to_prop lit)) && not (aux @@ Not (lit_to_prop lit))
  in
  let check_valid_pre prop =
    not
      (Prover.check_valid (smart_forall qvs @@ smart_implies gprop (Not prop)))
  in
  let check_valid abd =
    let p =
      smart_forall qvs @@ smart_exists local_vs
      @@ smart_implies (smart_add_to abd gprop) prop
    in
    let () = Printf.printf "check: %s\n" @@ layout_prop p in
    Prover.check_valid p
  in
  if check_valid mk_true then Some mk_true
  else
    let cs = get_consts prop in
    let lits =
      List.map (fun x -> (AVar x) #: x.ty) qvs
      @ List.map (fun c -> (AC c) #: (constant_to_nt c)) cs
    in
    let fvtab = build_fvtab lits in
    (* let () = *)
    (*   Printf.printf "fvtab: %s\n" @@ List.split_by_comma layout_lit @@ fvtab *)
    (* in *)
    let fvtab = List.filter check_valid_feature fvtab in
    let fvs = List.init (List.length fvtab) (fun _ -> [ true; false ]) in
    let fvs = List.choose_list_list fvs in
    let fvs =
      List.map
        smart_and
        #. (List.mapi (fun idx x ->
                let lit = lit_to_prop @@ List.nth fvtab idx in
                if x then lit else Not lit))
        fvs
    in
    let fvs = List.filter check_valid_pre fvs in
    let fvs = List.filter check_valid fvs in
    let () = Printf.printf "res: %s\n" @@ layout_prop (smart_or fvs) in
    match fvs with [] -> None | _ -> Some (smart_or fvs)

let abduction ({ qvs; global_prop; _ } as goal) args (vs, cur_phi, phi) =
  let prop = smart_add_to cur_phi phi in
  let ctx = add_to_rights emp @@ List.map qv_to_cqv qvs @ args in
  let qvs, gprop = rctx_to_prefix ctx in
  let gprop = smart_add_to global_prop gprop in
  abduction_prop (qvs, vs, gprop, prop)

let mk_raw_all env =
  let l =
    List.map (fun x -> EffEvent { op = x.x; vs = x.ty; phi = mk_true })
    @@ ctx_to_list env.event_tyctx
  in
  if List.length l == 0 then _die [%here] else SFA.CharSet.of_list l

let parallel_interleaving_to_trace env l =
  let all = Star (MultiChar (mk_raw_all env)) in
  all
  :: List.concat_map (fun r -> [ MultiChar (SFA.CharSet.singleton r); all ]) l

let trace_to_raw_regex = function
  | [] -> Eps
  | _ as l -> List.left_reduce [%here] SFA.alt l

let inter_trace env { qvs; global_prop; reg = tr1, tr2 } =
  let r1, r2 = map2 trace_to_raw_regex (tr1, tr2) in
  let reg = Inters (r1, r2) in
  normalize_goal env { qvs; global_prop; reg }

(* let single_insert_into_trace se trace = *)
(*   let rec aux (res, pre) = function *)
(*     | [] -> res *)
(*     | Star r :: rest -> *)
(*         aux *)
(*           ( ( pre @ [ Star r ], *)
(*               [ MultiChar (SFA.CharSet.singleton se) ], *)
(*               [ Star r ] @ rest ) *)
(*             :: res, *)
(*             pre @ [ Star r ] ) *)
(*           rest *)
(*     | MultiChar cs :: rest -> aux (res, pre @ [ MultiChar cs ]) rest *)
(*     | _ -> _die [%here] *)
(*   in *)
(*   aux ([], []) trace *)

(* let rec insert_into_trace ses trace = *)
(*   match ses with *)
(*   | [] -> [ trace ] *)
(*   | [ se ] -> *)
(*       List.map (fun (a, b, c) -> a @ b @ c) @@ single_insert_into_trace se trace *)
(*   | se :: rest -> *)
(*       let l = single_insert_into_trace se trace in *)
(*       List.concat_map *)
(*         (fun (a, b, trace) -> *)
(*           let trace' = insert_into_trace rest trace in *)
(*           List.map (fun c -> a @ b @ c) trace') *)
(* l *)

let trace_divide_by_se se trace =
  let open SFA in
  let rec aux pre = function
    | [] -> _die_with [%here] "never"
    | MultiChar s :: post -> (
        match List.of_seq @@ CharSet.to_seq s with
        | [ x ] ->
            if equal_sevent Nt.equal_nt se x then (pre, post)
            else aux (pre @ [ MultiChar s ]) post
        | _ -> _die [%here])
    | Star r :: post -> aux (pre @ [ Star r ]) post
    | _ -> _die [%here]
  in
  aux [] trace

let clearn_trace trace =
  List.filter_map
    (function
      | MultiChar c -> Some (charset_to_se [%here] c)
      | Star _ -> None
      | _ -> _die [%here])
    trace

let check_regex_include env checker (r1, r2) =
  (* let () = *)
  (*   Printf.printf "<<<: %s <: %s\n" (SFA.layout_raw_regex r1) *)
  (*     (SFA.layout_raw_regex r2) *)
  (* in *)
  let all = mk_raw_all env in
  let goals =
    Desymbolic.desymbolic_reg OriginalFA env.event_tyctx checker
      ([], SFA.raw_regex_to_regex (Inters (r1, Comple (all, r2))))
  in
  List.for_all
    (fun (_, _, reg) ->
      let open DesymFA in
      let dfa = compile_regex_to_dfa reg in
      let dfa = minimize dfa in
      (* let () = Printf.printf "dfa:\n%s\n" (layout_dfa dfa) in *)
      StateSet.is_empty dfa.finals)
    goals

let cur_to_obs { op; vs; phi } =
  let args = List.map (fun x -> (Rename.unique x.x) #: x.ty) vs in
  let phi =
    List.fold_right
      (fun (x, y) p -> subst_prop_instance x.x (AVar y) p)
      (_safe_combine [%here] vs args)
      phi
  in
  let vargs = List.map (fun x -> VVar x) args in
  (args, phi, PlanObs { vargs; op })

let to_conjs prop =
  let rec aux = function And l -> List.concat_map aux l | _ as r -> [ r ] in
  aux prop

let to_lit_opt = function Lit lit -> Some lit.x | _ -> None
let is_var_c = function AVar _ | AC _ -> true | _ -> false

let lit_to_equation = function
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x ->
      if is_var_c a.x && is_var_c b.x then Some (a.x, b.x) else None
  | _ -> None

let simp_eq_lit lit =
  match lit with
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x ->
      if equal_lit Nt.equal_nt a.x b.x then AC (B true) else lit
  | _ -> lit

let simpl_eq_in_prop =
  let rec aux = function
    | Lit lit -> Lit (simp_eq_lit lit.x) #: lit.ty
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not p ->
        let p = aux p in
        if is_true p then mk_false else if is_false p then mk_true else Not p
    | And es -> smart_and (List.map aux es)
    | Or es -> smart_or (List.map aux es)
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Forall { qv; body } -> Forall { qv; body = aux body }
    | Exists { qv; body } -> Exists { qv; body = aux body }
  in
  aux

let eq_in_prop_to_subst_map (qvs, prop) =
  let conjs = to_conjs prop in
  let lits = List.filter_map to_lit_opt conjs in
  let eqs = List.filter_map lit_to_equation lits in
  let eqcs, eqvs =
    List.partition
      (function x, AVar _ -> false | x, AC _ -> true | _ -> _die [%here])
      eqs
  in
  let subst_eqs x lit = List.map (map2 (subst_lit_instance x lit)) in
  let rec aux (eqs, res) =
    match eqs with
    | [] -> res
    | (AVar x, AVar y) :: eqs ->
        let comp a b =
          let c = compare (String.length a) (String.length b) in
          if c == 0 then compare a b else c
        in
        let c = comp x.x y.x in
        (* let () = Printf.printf "\tCompare %s %s = %i\n" x.x y.x c in *)
        if c == 0 then aux (eqs, res)
        else if c > 0 then
          let res = res @ [ (x.x, AVar y) ] in
          let eqs = subst_eqs x.x (AVar y) eqs in
          aux (eqs, res)
        else
          let res = res @ [ (y.x, AVar x) ] in
          let eqs = subst_eqs y.x (AVar x) eqs in
          aux (eqs, res)
    | (AVar x, AC c | AC c, AVar x) :: eqs ->
        let res = res @ [ (x.x, AC c) ] in
        let eqs = subst_eqs x.x (AC c) eqs in
        aux (eqs, res)
    | (AC _, AC _) :: eqs -> aux (eqs, res)
    | _ -> _die [%here]
  in
  let m = aux (eqs, []) in
  let prop =
    List.fold_right (fun (x, lit) -> subst_prop_instance x lit) m prop
  in
  let qvs =
    List.filter
      (fun x -> not (List.exists (fun (y, _) -> String.equal x.x y) m))
      qvs
  in
  let prop = simpl_eq_in_prop prop in
  ((qvs, prop), m)

let optimize_back_goal
    ({ qvs; global_prop; reg = a, b, c } as goal :
      (plan * plan_elem * plan) sgoal) =
  let (qvs, global_prop), m = eq_in_prop_to_subst_map (qvs, global_prop) in
  let a, c = map2 (Plan.msubst Plan.subst_plan m) (a, c) in
  let b = Plan.msubst Plan.subst_elem m b in
  let goal' = { qvs; global_prop; reg = (a, b, c) } in
  let () =
    Printf.printf "Optimize:\n";
    layout_syn_back_judgement goal;
    Printf.printf "==>\n";
    layout_syn_back_judgement goal'
  in
  goal'

let optimize_goal ({ qvs; global_prop; reg } as goal : plan sgoal) =
  let (qvs, global_prop), m = eq_in_prop_to_subst_map (qvs, global_prop) in
  { qvs; global_prop; reg = Plan.msubst Plan.subst_plan m reg }

let rec deductive_synthesis_reg env goal : plan sgoal option =
  let goals = normalize_goal env goal in
  let res = List.filter_map (deductive_synthesis_trace env) goals in
  match res with [] -> None | g :: _ -> Some g

and deductive_synthesis_trace env goal : plan sgoal option =
  (* let goal = map_goal raw_regex_to_trace goal in *)
  let () = layout_syn_plan_judgement goal in
  let rec handle goal =
    match Plan.right_most_se goal.reg with
    | None -> Some goal
    | Some (pre, cur, post) ->
        let args, gprop', obs_elem = cur_to_obs cur in
        let subgoal =
          {
            qvs = goal.qvs @ args;
            global_prop = smart_add_to gprop' goal.global_prop;
            reg = (pre, obs_elem, post);
          }
        in
        let* goal = backward env subgoal in
        let () = Printf.printf "next step\n" in
        let () = layout_syn_plan_judgement goal in
        handle goal
  in
  (* let* res = *)
  (*   List.fold_left *)
  (*     (fun goal subgoal -> *)
  (*       match goal with *)
  (*       | None -> _die [%here] *)
  (*       | Some goal -> handle goal subgoal) *)
  (*     (Some goal) subgoals *)
  (* in *)
  let* goal = handle goal in
  let goal = map_goal (Plan.remove_star [%here]) goal in
  Some goal

(* let rec aux res (pre, post) = *)
(*   match post with *)
(*   | [] -> res *)
(*   | MultiChar cs :: post -> *)
(*       let cur = mk_cur [%here] (MultiChar cs) in *)
(*       aux ((pre, cur, post) :: res) (pre @ [ MultiChar cs ], post) *)
(*   | x :: post -> aux res (pre @ [ x ], post) *)
(* in *)
(* let tasks = aux [] ([], goal.reg) in *)
(* let goals = List.map (fun reg -> map_goal (fun _ -> reg) goal) tasks in *)
(* let res = backtrack (backward env) goals in *)
(* None *)

and backward env
    ({ qvs; global_prop; reg = pre, elem, post } as goal :
      (plan * plan_elem * plan) sgoal) : plan sgoal option =
  let () = layout_syn_back_judgement goal in
  let op, elem_args =
    match elem with PlanObs { op; vargs } -> (op, vargs) | _ -> _die [%here]
  in
  if _get_force [%here] env.gen_ctx op then
    let elem = PlanGen { op; vargs = elem_args } in
    Some { qvs; global_prop; reg = pre @ [ elem ] @ post }
  else
    let handle (se, haft) =
      let () =
        Printf.printf "handle se: %s haft: %s\n" (layout_se se)
          (layout_haft SFA.layout_raw_regex haft)
      in
      let args, retrty = destruct_haft [%here] haft in
      let history, dep_se, p = destruct_hap [%here] retrty in
      let () = Printf.printf "dep_se: %s\n" (layout_se dep_se) in
      let dep_elem =
        PlanObs
          {
            op = _get_sevent_name [%here] dep_se;
            vargs = List.map (fun x -> VVar x.x #: x.ty.nt) args;
          }
      in
      let () = Printf.printf "dep_elem: %s\n" (Plan.layout_elem dep_elem) in
      let* gprop =
        let _, _, phi' = _get_sevent_fields [%here] se in
        let { op; vs; phi } = Plan.elem_to_cur env.event_tyctx elem in
        abduction goal args (vs, phi, phi')
      in
      let args = List.map (fun x -> x.x #: x.ty.nt) args in
      let qvs = qvs @ args in
      let global_prop = smart_add_to gprop global_prop in
      let qvs, global_prop, p =
        List.fold_left
          (fun (qvs, global_prop, p) se ->
            let args, phi, elem = cur_to_obs @@ se_to_cur [%here] se in
            (qvs @ args, smart_add_to phi global_prop, p @ [ elem ]))
          (qvs, global_prop, []) p
      in
      let fs = Plan.parallel_interleaving p in
      (* let fs = List.map (map2 (parallel_interleaving_to_trace env)) fs in *)
      let check_include =
        check_regex_include env (fun (_, prop) ->
            let p = smart_add_to global_prop prop in
            (* let () = Printf.printf "CheckSet: %s\n" (layout_prop p) in *)
            Prover.check_sat_bool (smart_add_to global_prop prop))
      in
      let goals =
        List.concat_map
          (fun (f11, f12) ->
            let posts = Plan.insert env.event_tyctx check_include f12 post in
            (* let old_cur = EffEvent { op; vs; phi = smart_add_to phi' phi } in *)
            let f11' = dep_elem :: f11 in
            let pres =
              List.map (Plan.divide_by_elem dep_elem)
              @@ Plan.insert env.event_tyctx check_include f11' pre
            in
            let goals =
              List.map (fun ((pre1, pre2), post) ->
                  {
                    qvs;
                    global_prop;
                    reg = (pre1, dep_elem, pre2 @ [ elem ] @ post);
                  })
              @@ List.cross pres posts
            in
            goals)
          fs
      in
      (* let () = List.iter layout_syn_tmp_judgement goals in *)
      (* let () = List.iter layout_syn_back_judgement goals in *)
      Some goals
    in
    let rules = select_rule_by_future env op in
    let () =
      List.iteri
        (fun i (se, haft) ->
          let () =
            Printf.printf "rule[%i] se: %s haft: %s\n" i (layout_se se)
              (layout_haft SFA.layout_raw_regex haft)
          in
          ())
        rules
    in
    let goals = List.concat @@ List.filter_map handle rules in
    let goals = List.map optimize_back_goal goals in
    backtrack (backward env) goals

let quantifier_elimination (qvs, gprop, qv, local_qvs, prop) =
  let () = Printf.printf "remove qv: %s\n" (layout_qv qv) in
  let () = Printf.printf "qvs: %s\n" (layout_qvs qvs) in
  let () = Printf.printf "prop: %s\n" (layout_prop prop) in
  let check_valid_feature lit =
    let aux prop =
      Prover.check_valid (smart_forall (qv :: qvs) @@ smart_implies gprop prop)
    in
    (not (aux @@ lit_to_prop lit)) && not (aux @@ Not (lit_to_prop lit))
  in
  let check_valid_pre prop =
    not
      (Prover.check_valid
         (smart_forall (qv :: qvs) @@ smart_implies gprop (Not prop)))
  in
  let check_valid abd =
    let p =
      smart_forall (qv :: qvs)
      @@ smart_exists local_qvs @@ smart_exists qvs
      @@ smart_implies (smart_add_to abd gprop) prop
    in
    let () = Printf.printf "check: %s\n" @@ layout_prop p in
    Prover.check_valid p
  in
  if check_valid mk_true then Some mk_true
  else
    let cs = get_consts prop in
    let lits =
      List.map (fun x -> (AVar x) #: x.ty) qvs
      @ List.map (fun c -> (AC c) #: (constant_to_nt c)) cs
    in
    let lits = List.filter (fun lit -> Nt.equal_nt qv.ty lit.ty) lits in
    let fvtab =
      List.map (fun lit -> mk_lit_eq_lit qv.ty (AVar qv) lit.x) lits
    in
    let () =
      Printf.printf "fvtab: %s\n" @@ List.split_by_comma layout_lit @@ fvtab
    in
    let fvs = List.init (List.length fvtab) (fun _ -> [ true; false ]) in
    let fvs = List.choose_list_list fvs in
    let fvs =
      List.map
        smart_and
        #. (List.mapi (fun idx x ->
                let lit = lit_to_prop @@ List.nth fvtab idx in
                if x then lit else Not lit))
        fvs
    in
    let fvs = List.filter check_valid fvs in
    (* let () = Printf.printf "res: %s\n" @@ layout_prop (smart_or fvs) in *)
    match fvs with [] -> None | _ -> Some (smart_or fvs)

let rec to_top_cnf phi =
  match phi with And ps -> List.concat_map to_top_cnf ps | _ -> [ phi ]

let tv_mem vs qv = List.exists (fun x -> String.equal x.x qv.x) vs
let tv_not_mem vs qv = not (tv_mem vs qv)
let tv_to_lit x = (AVar x) #: x.ty
let c_to_lit c = (AC c) #: (constant_to_nt c)

module Gamma = struct
  type gamma = { bvs : (Nt.nt, string) typed list; bprop : Nt.nt prop }

  let mem { bvs; _ } = tv_mem bvs
  let not_mem { bvs; _ } = tv_not_mem bvs
  let emp = { bvs = []; bprop = mk_true }

  let layout { bvs; bprop } =
    spf "{%s | %s}" (layout_qvs bvs) (layout_prop bprop)
end

let instantiation_var (gamma : Gamma.gamma) vs ({ qvs; global_prop; _ } as goal)
    =
  let cs = get_consts global_prop in
  let lits = List.map tv_to_lit (gamma.bvs @ vs) @ List.map c_to_lit cs in
  let fvtab = build_fvtab lits in
  let fvtab =
    List.filter
      (fun lit ->
        let s =
          List.interset String.equal (List.map _get_x vs) (fv_lit_id lit)
        in
        not (List.is_empty s))
      fvtab
  in
  let check_valid_feature lit =
    let aux prop =
      Prover.check_valid
        (smart_forall gamma.bvs @@ smart_implies gamma.bprop prop)
    in
    (not (aux @@ lit_to_prop lit)) && not (aux @@ Not (lit_to_prop lit))
  in
  let check_valid_pre prop =
    not
      (Prover.check_valid
         (smart_forall gamma.bvs @@ smart_implies gamma.bprop (Not prop)))
  in
  let check_valid abd =
    let p =
      smart_forall (gamma.bvs @ vs)
      @@ smart_exists qvs
      @@ smart_implies (smart_add_to abd gamma.bprop) global_prop
    in
    let () = Printf.printf "check: %s\n" @@ layout_prop p in
    Prover.check_valid p
  in
  let fvs = List.init (List.length fvtab) (fun _ -> [ true; false ]) in
  let fvs = List.choose_list_list fvs in
  let fvs =
    List.map
      smart_and
      #. (List.mapi (fun idx x ->
              let lit = lit_to_prop @@ List.nth fvtab idx in
              if x then lit else Not lit))
      fvs
  in
  let fvs = List.filter check_valid_pre fvs in
  let fvs = List.filter check_valid fvs in
  let () = Printf.printf "res: %s\n" @@ layout_prop (smart_or fvs) in
  match fvs with
  | [] -> _die [%here]
  | _ ->
      let bprop' = smart_or fvs in
      let gamma =
        Gamma.{ bvs = gamma.bvs @ vs; bprop = smart_add_to bprop' gamma.bprop }
      in
      (gamma, bprop')

let instantiation env goal =
  let get_fvargs gamma vargs qvs =
    let args =
      List.filter_map (function VVar x -> Some x | _ -> None) vargs
    in
    let args = List.filter (Gamma.not_mem gamma) args in
    let qvs' = List.filter (tv_not_mem args) qvs in
    let () =
      Printf.printf
        "get_fvargs:::\n\
         gamma: %s $$$ vargs: %s $$$ qvs: %s\n\
         ==>args: %s $$$ qvs: %s\n"
        (layout_qvs gamma.bvs)
        (List.split_by_comma layout_value vargs)
        (layout_qvs qvs) (layout_qvs args) (layout_qvs qvs')
    in
    (args, qvs')
  in
  let rec handle gamma ({ qvs; global_prop; reg = plan } as goal) =
    let () =
      Printf.printf "Gamma: %s\n" (Gamma.layout gamma);
      layout_syn_plan_judgement goal
    in
    match plan with
    | [] -> if 0 == List.length qvs then mk_term_tt else _die [%here]
    | PlanGen { op; vargs } :: plan ->
        let fargs, qvs = get_fvargs gamma vargs qvs in
        let goal = { goal with reg = plan; qvs } in
        let gamma, prop' = instantiation_var gamma fargs goal in
        let e = handle gamma goal in
        let e = mk_term_assertP prop' @@ mk_term_gen env op vargs e in
        let e =
          List.fold_right (fun x -> mk_let [ x ] (CRandom x.ty)) fargs e
        in
        e
    | PlanObs { op; vargs } :: plan ->
        let fargs, qvs = get_fvargs gamma vargs qvs in
        let goal = { goal with reg = plan; qvs } in
        let gamma, prop' = instantiation_var gamma fargs goal in
        (* let () = _die [%here] in *)
        let e = handle gamma goal in
        let args' =
          List.map
            (function
              | VVar x when name_in_qvs x.x fargs -> x
              | _ as v -> (Rename.unique "tmp") #: (value_to_nt v))
            vargs
        in
        let ps =
          List.filter_map (fun (x, y) ->
              if equal_value (VVar x) y then None
              else
                let lit = mk_lit_eq_lit x.ty (AVar x) (value_to_lit y) in
                Some (lit_to_prop lit))
          @@ _safe_combine [%here] args' vargs
        in
        let p = smart_and (ps @ [ prop' ]) in
        let e = mk_term_obs env op args' (mk_term_assertP p e) in
        e
    | _ :: _ -> _die [%here]
  in
  let prog = handle Gamma.emp goal in
  let () = Pp.printf "@{<bold>Prog@}:\n%s\n" (layout_term prog) in
  prog

let synthesize env goal =
  let* goal = deductive_synthesis_reg env goal in
  let () = Printf.printf "Result: %s\n" (Plan.layout_plan goal.reg) in
  let _ = instantiation env goal in
  None
(* Some (reverse_instantiation env res) *)

let test env =
  let _ = synthesize env @@ mk_synthesis_goal env in
  ()

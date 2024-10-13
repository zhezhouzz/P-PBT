open Language

type sregex = Nt.t sevent raw_regex
type 'a sgoal = Gamma.gamma * 'a

(* type 'a sgoal = { *)
(*   qvs : (Nt.t, string) typed list; *)
(*   bprop : Nt.t prop; *)
(*   reg : 'a; *)
(* } *)

(* let map_goal f { qvs; bprop; reg } = { qvs; bprop; reg = f reg } *)

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
  (Gamma.{ bvs = qvs; bprop = mk_true }, SFA.regex_to_raw reg)

let layout_planing_judgement gamma str =
  let open Gamma in
  let ctx_str =
    spf "%s | %s" (layout_qvs gamma.bvs) (layout_prop gamma.bprop)
  in
  Printf.printf "%s|- %s\n\n" ctx_str str

let layout_syn_reg_judgement (gamma, reg) =
  layout_planing_judgement gamma (SFA.layout_raw_regex reg)

let layout_syn_plan_judgement (gamma, reg) =
  (* layout_planing_judgement gamma (Plan.layout reg) *)
  layout_planing_judgement gamma (Plan.omit_layout reg)

let layout_syn_back_judgement (gamma, (pre, cur, post)) =
  let open Plan in
  layout_planing_judgement gamma
    (spf "back [%s] %s [%s]" (omit_layout pre) (layout_elem cur)
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
(*     spf "%s | %s" (layout_qvs goal.qvs) (layout_prop goal.bprop) *)
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

(* [@@@warning "-27"] *)
(* [@@@warning "-26"] *)

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

let charset_to_se loc s =
  let open SFA in
  match List.of_seq @@ CharSet.to_seq s with [ x ] -> x | _ -> _die loc

let se_to_raw_regex se = MultiChar (SFA.CharSet.singleton se)

let raw_regex_to_cs r =
  let open SFA in
  let rec aux r =
    match r with
    | MultiChar cs -> Some cs
    | Comple (cs, r) ->
        let* cs' = aux r in
        let cs =
          CharSet.filter_map
            (fun se ->
              let op, vs, phi = _get_sevent_fields [%here] se in
              let phis =
                CharSet.fold
                  (fun se' phis ->
                    let op', _, phi' = _get_sevent_fields [%here] se' in
                    if String.equal op op' then phi' :: phis else phis)
                  cs' []
              in
              let phi = smart_add_to phi (Not (smart_or phis)) in
              match phi with
              | Not p when is_true p -> None
              | _ -> Some (EffEvent { op; vs; phi }))
            cs
        in
        Some cs
    | Inters (r1, r2) ->
        let* cs1 = aux r1 in
        let* cs2 = aux r2 in
        let cs =
          CharSet.filter_map
            (fun se ->
              let op, vs, phi = _get_sevent_fields [%here] se in
              let phis =
                CharSet.fold
                  (fun se' phis ->
                    let op', _, phi' = _get_sevent_fields [%here] se' in
                    if String.equal op op' then phi' :: phis else phis)
                  cs2 []
              in
              let phi = smart_add_to phi (smart_or phis) in
              if is_false phi then None else Some (EffEvent { op; vs; phi }))
            cs1
        in
        Some cs
    | _ -> None
  in
  aux r

let raw_regex_to_plan_elem r =
  let open SFA in
  let r = unify_raw_regex r in
  match r with
  | MultiChar cs ->
      let se = charset_to_se [%here] cs in
      let op, vs, phi = _get_sevent_fields [%here] se in
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

let add_global_prop_to_se p = function
  | EffEvent { op; vs; phi } -> EffEvent { op; vs; phi = smart_add_to p phi }
  | _ -> _die [%here]

let add_global_prop_to_raw_reg prop =
  let open SFA in
  let rec aux r =
    match r with
    | Empty | Eps -> r
    | MultiChar cs -> MultiChar (CharSet.map (add_global_prop_to_se prop) cs)
    | Alt (r1, r2) -> Alt (aux r1, aux r2)
    | Seq l -> Seq (List.map aux l)
    | Star r -> Star (aux r)
    | Inters (r1, r2) -> Inters (r1, r2)
    | Comple (cs, r) ->
        Comple (CharSet.map (add_global_prop_to_se prop) cs, aux r)
  in
  aux

let reduce_symbolic_regex env checker r =
  let open SFA in
  let r = unify_raw_regex r in
  let rec aux r =
    match r with
    | Empty | Eps | MultiChar _ -> [ (mk_true, r) ]
    | Alt (r1, r2) -> aux r1 @ aux r2
    | Seq [] -> [ (mk_true, Eps) ]
    | Seq (r :: rs) ->
        let r2 = aux (Seq rs) in
        let r1 = aux r in
        List.map (fun ((p1, r1), (p2, r2)) ->
            (smart_add_to p1 p2, seq [ r1; r2 ]))
        @@ List.cross r1 r2
    | Star r ->
        let l =
          Desymbolic.desymbolic_reg OriginalFA env.event_tyctx checker
            ([], SFA.raw_regex_to_regex r)
        in
        let l =
          List.map
            (fun (bprop, backward_maping, reg) ->
              (bprop, raw_reg_map backward_maping (DesymFA.regex_to_raw reg)))
            l
        in
        let ps, rs = List.split l in
        [ (smart_and ps, Star (alt_list rs)) ]
    | Inters _ | Comple _ ->
        let l =
          Desymbolic.desymbolic_reg OriginalFA env.event_tyctx checker
            ([], SFA.raw_regex_to_regex r)
        in
        let l =
          List.map
            (fun (bprop, backward_maping, reg) ->
              (bprop, raw_reg_map backward_maping (DesymFA.regex_to_raw reg)))
            l
        in
        l
  in
  List.map (fun (p, r) -> (p, unify_raw_regex r)) @@ aux r

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

(* let normalize_goal env ({ bvs; bprop = old_bprop }, reg) = *)
(*   let () = *)
(*     Pp.printf "\n@{<bold>Before Normalize:@}\n%s\n" (SFA.layout_raw_regex reg) *)
(*   in *)
(*   let checker (_, prop) = *)
(*     let () = Printf.printf "check: %s\n" (layout_prop prop) in *)
(*     Prover.check_sat_bool (And [ old_bprop; prop ]) *)
(*   in *)
(*   let reg = reduce_symbolic_regex env checker reg in *)
(*   List.map *)
(*     (fun (p, r) -> *)
(*       ({ bvs; bprop = smart_add_to p old_bprop }, raw_regex_to_plan r)) *)
(*     reg *)

let normalize_desym_regex2 (rawreg : DesymFA.raw_regex) =
  let open DesymFA in
  (* let () = Pp.printf "@{<bold>start@}: %s\n" (layout_raw_regex rawreg) in *)
  let rec aux rawreg =
    match rawreg with
    | Empty | Eps | MultiChar _ -> rawreg
    | Alt (r1, r2) -> alt (aux r1) (aux r2)
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
    | Seq l -> seq (List.map aux l)
    | Star r -> Star (do_normalize_desym_regex r)
  in
  aux rawreg

let normalize_goal env ({ bvs; bprop = old_bprop }, reg) =
  let () =
    Pp.printf "\n@{<bold>Before Normalize:@}\n%s\n" (SFA.layout_raw_regex reg)
  in
  let checker (_, prop) =
    let () = Printf.printf "check: %s\n" (layout_prop prop) in
    Prover.check_sat_bool (And [ old_bprop; prop ])
  in
  let goals =
    Desymbolic.desymbolic_reg OriginalFA env.event_tyctx checker
      (bvs, SFA.raw_regex_to_regex reg)
  in
  let open DesymFA in
  let goals =
    List.concat_map
      (fun (bprop, backward_maping, reg) ->
        let () =
          Printf.printf "reg: %s\n" (layout_raw_regex (regex_to_raw reg))
        in
        let reg = normalize_desym_regex2 @@ regex_to_raw reg in
        let () = Pp.printf "@{<bold>reg@}: %s\n" (layout_raw_regex reg) in
        if is_empty_raw_regex reg then []
        else
          let unf =
            DesymFA.raw_regex_to_union_normal_form unify_charset_by_op reg
          in
          let unf = List.map (List.map (raw_reg_map backward_maping)) unf in
          let unf =
            List.map
              (fun l ->
                ( { bvs; bprop = smart_add_to bprop old_bprop },
                  List.map raw_regex_to_plan_elem l ))
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

(* let abduction ({ qvs; bprop; _ } as goal) args (vs, cur_phi, phi) = *)
(*   let prop = smart_add_to cur_phi phi in *)
(*   let ctx = add_to_rights emp @@ List.map qv_to_cqv qvs @ args in *)
(*   let qvs, gprop = rctx_to_prefix ctx in *)
(*   let gprop = smart_add_to bprop gprop in *)
(*   abduction_prop (qvs, vs, gprop, prop) *)

(* let mk_raw_all env = *)
(*   let l = *)
(*     List.map (fun x -> EffEvent { op = x.x; vs = x.ty; phi = mk_true }) *)
(*     @@ ctx_to_list env.event_tyctx *)
(*   in *)
(*   if List.length l == 0 then _die [%here] else SFA.CharSet.of_list l *)

(* let parallel_interleaving_to_trace env l = *)
(*   let all = Star (MultiChar (mk_raw_all env)) in *)
(*   all *)
(*   :: List.concat_map (fun r -> [ MultiChar (SFA.CharSet.singleton r); all ]) l *)

(* let trace_to_raw_regex = function *)
(*   | [] -> Eps *)
(*   | _ as l -> List.left_reduce [%here] SFA.alt l *)

(* let inter_trace env { qvs; bprop; reg = tr1, tr2 } = *)
(*   let r1, r2 = map2 trace_to_raw_regex (tr1, tr2) in *)
(*   let reg = Inters (r1, r2) in *)
(*   normalize_goal env { qvs; bprop; reg } *)

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

(* let check_regex_include env checker (r1, r2) = *)
(*   (\* let () = *\) *)
(*   (\*   Printf.printf "<<<: %s <: %s\n" (SFA.layout_raw_regex r1) *\) *)
(*   (\*     (SFA.layout_raw_regex r2) *\) *)
(*   (\* in *\) *)
(*   let all = mk_raw_all env in *)
(*   let goals = *)
(*     Desymbolic.desymbolic_reg OriginalFA env.event_tyctx checker *)
(*       ([], SFA.raw_regex_to_regex (Inters (r1, Comple (all, r2)))) *)
(*   in *)
(*   List.for_all *)
(*     (fun (_, _, reg) -> *)
(*       let open DesymFA in *)
(*       let dfa = compile_regex_to_dfa reg in *)
(*       let dfa = minimize dfa in *)
(*       (\* let () = Printf.printf "dfa:\n%s\n" (layout_dfa dfa) in *\) *)
(*       StateSet.is_empty dfa.finals) *)
(*     goals *)

let cur_to_obs { op; vs; phi } =
  let args = List.map (fun x -> (Rename.unique x.x) #: x.ty) vs in
  let phi =
    List.fold_right
      (fun (x, y) p -> subst_prop_instance x.x (AVar y) p)
      (_safe_combine [%here] vs args)
      phi
  in
  (args, phi, PlanActBuffer { args; op; phi })

let lit_to_equation = function
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x ->
      if is_var_c a.x && is_var_c b.x then Some (a.x, b.x) else None
  | _ -> None

let eq_in_prop_to_subst_map { bvs; bprop } =
  let conjs = to_conjs bprop in
  let lits = List.filter_map to_lit_opt conjs in
  let eqs = List.filter_map lit_to_equation lits in
  let eqvs =
    List.filter_map (function AVar x, AVar y -> Some (x, y) | _ -> None) eqs
  in
  let subst_eqs x lit = List.map (map2 (subst_name_qv x lit)) in
  let rec aux (eqs, res) =
    match eqs with
    | [] -> res
    | (x, y) :: eqs ->
        let comp a b =
          let c = compare (String.length a) (String.length b) in
          if c == 0 then compare a b else c
        in
        let c = comp x.x y.x in
        (* let () = Printf.printf "\tCompare %s %s = %i\n" x.x y.x c in *)
        if c == 0 then aux (eqs, res)
        else if c > 0 then
          let res = res @ [ (x.x, y) ] in
          let eqs = subst_eqs x.x y eqs in
          aux (eqs, res)
        else
          let res = res @ [ (y.x, x) ] in
          let eqs = subst_eqs y.x x eqs in
          aux (eqs, res)
  in
  let m = aux (eqvs, []) in
  let prop =
    List.fold_right (fun (x, lit) -> subst_prop_instance x (AVar lit)) m bprop
  in
  let bvs =
    List.filter
      (fun x -> not (List.exists (fun (y, _) -> String.equal x.x y) m))
      bvs
  in
  let bprop = simpl_eq_in_prop prop in
  ({ bvs; bprop }, m)

let optimize_back_goal ((gamma, (a, b, c)) as goal) =
  let gamma, m = eq_in_prop_to_subst_map gamma in
  let a, c = map2 (msubst Plan.subst_plan m) (a, c) in
  let b = msubst Plan.subst_elem m b in
  let goal' = (gamma, (a, b, c)) in
  let () =
    Printf.printf "Optimize:\n";
    layout_syn_back_judgement goal;
    Printf.printf "==>\n";
    layout_syn_back_judgement goal'
  in
  goal'

let optimize_goal ((gamma, reg) : plan sgoal) =
  let gamma, m = eq_in_prop_to_subst_map gamma in
  (gamma, msubst Plan.subst_plan m reg)

let preserve_goals = ref SFA.CharSet.empty

let mk_preserve_subgoal plan =
  preserve_goals :=
    SFA.CharSet.of_list
    @@ List.filter_map
         (function PlanSe cur -> Some (cur_to_se cur) | _ -> None)
         plan

let remove_preserve_subgoal elem =
  preserve_goals :=
    SFA.CharSet.remove
      (match elem with PlanSe cur -> cur_to_se cur | _ -> _die [%here])
      !preserve_goals

let in_preserve_subgoal elem =
  SFA.CharSet.mem
    (match elem with PlanSe cur -> cur_to_se cur | _ -> _die [%here])
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
  let () =
    Pp.printf "@{<green>right most@} se[%s] in %s\n" (layout_cur cur)
      (layout plan)
  in
  (* let () = if !counter >= 2 then _die [%here] in *)
  Some (List.rev post, cur, List.rev pre)

let rec deductive_synthesis_reg env goal : plan sgoal option =
  let goals = normalize_goal env goal in
  let res = List.filter_map (deductive_synthesis_trace env) goals in
  match res with [] -> None | g :: _ -> Some g

and deductive_synthesis_trace env goal : plan sgoal option =
  (* let goal = map_goal raw_regex_to_trace goal in *)
  let () = layout_syn_plan_judgement goal in
  let rec handle ((gamma, reg) as goal) =
    (* let () = if !counter >= 2 then _die [%here] in *)
    match right_most_se reg with
    | None -> Some goal
    | Some (pre, cur, post) ->
        let args, gprop', obs_elem = cur_to_obs cur in
        let subgamma =
          { bvs = gamma.bvs @ args; bprop = smart_add_to gprop' gamma.bprop }
        in
        let subgoal = (subgamma, (pre, obs_elem, post)) in
        (* let () = remove_preserve_subgoal obs_elem in *)
        let* goal = backward env subgoal in
        let () = Printf.printf "next step\n" in
        let () = layout_syn_plan_judgement goal in
        (* let () = counter := !counter + 1 in *)
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
  let () = mk_preserve_subgoal (snd goal) in
  let* gamma, reg = handle goal in
  Some (gamma, Plan.remove_star [%here] reg)

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

(* and forward_one ({ bvs; bprop }, (pre, elem, post)) = *)
(*   match elem with *)
(*   | PlanSe cur -> *)
(*       let args, phi, elem = cur_to_obs cur in *)
(*       let gamma = { bvs = bvs @ args; bprop = smart_add_to bprop phi } in *)
(*       (gamma, (pre, elem, post)) *)
(*   | _ -> ({ bvs; bprop }, (pre, elem, post)) *)

and forward (gamma, (pre, elem, post)) =
  let rec aux { bvs; bprop } solved rest =
    (* let () = *)
    (*   Pp.printf "@{<bold>forward:@} %s ;; %s\n" (Plan.layout solved) *)
    (*     (Plan.layout post) *)
    (* in *)
    match rest with
    | [] -> ({ bvs; bprop }, solved)
    | (PlanSe cur as elem) :: rest ->
        let () =
          Printf.printf "forward parse on cur: %s\n" (Plan.layout_elem elem)
        in
        if not (in_preserve_subgoal elem) then
          let args, phi, elem = cur_to_obs cur in
          let () = Printf.printf "do: %s\n" (Plan.layout_elem elem) in
          let gamma = { bvs = bvs @ args; bprop = smart_add_to bprop phi } in
          aux gamma (solved @ [ elem ]) rest
        else aux gamma (solved @ [ elem ]) rest
    | elem :: rest -> aux gamma (solved @ [ elem ]) rest
  in
  let gamma, post = aux gamma [] post in
  (gamma, (pre, elem, post))

and backward env (goal : (plan * plan_elem * plan) sgoal) : plan sgoal option =
  let () = layout_syn_back_judgement goal in
  let goal = forward goal in
  let gamma, (pre, elem, post) = goal in
  (* let op, elem_args = *)
  (*   match elem with PlanAct { op; args } -> (op, args) | _ -> _die [%here] *)
  (* in *)
  let op = Plan.elem_to_op [%here] elem in
  if is_gen env op then
    (* let () = if String.equal op "writeReq" then _die [%here] in *)
    Some (gamma, pre @ [ elem ] @ post)
  else
    let handle (se, haft) =
      let () =
        Printf.printf "handle se: %s haft: %s\n" (layout_se se)
          (layout_haft SFA.layout_raw_regex haft)
      in
      let elem =
        match Plan.smart_and_cur (se_to_cur [%here] se) elem with
        | Some x -> x
        | None -> _die [%here]
      in
      let args, retrty = destruct_haft [%here] haft in
      let history, dep_se, p = destruct_hap [%here] retrty in
      (* NOTE: history should be well-formed. *)
      let history_plan = raw_regex_to_plan history in
      let () = Printf.printf "dep_se: %s\n" (layout_se dep_se) in
      let dep_elem =
        (* NOTE: the payload should just conj of eq *)
        let op, _, _ = _get_sevent_fields [%here] dep_se in
        let args = List.map (fun x -> x.x #: x.ty.nt) args in
        PlanAct { op; args }
      in
      (* let () = Printf.printf "dep_elem: %s\n" (Plan.layout_elem dep_elem) in *)
      (* let* gprop = *)
      (*   let _, _, phi' = _get_sevent_fields [%here] se in *)
      (*   let { op; vs; phi } = Plan.elem_to_cur env.event_tyctx elem in *)
      (*   abduction goal args (vs, phi, phi') *)
      (* in *)
      let args, arg_phis = List.split @@ List.map destruct_cty_var args in
      let gamma = { gamma with bprop = smart_and (gamma.bprop :: arg_phis) } in
      (* let qvs, bprop, p = *)
      (*   List.fold_left *)
      (*     (fun (qvs, bprop, p) se -> *)
      (*       (\* let args, phi, elem = cur_to_obs @@ se_to_cur [%here] se in *\) *)
      (*        (qvs @ args, bprop, p @ [ PlanSe (se_to_cur [%here] se) ])) *)
      (*     (qvs, bprop, []) p *)
      (* in *)
      let p = List.map (fun se -> PlanSe (se_to_cur [%here] se)) p in
      let fs = Plan.parallel_interleaving p in
      let () =
        List.iter
          (fun (p1, p2) ->
            Pp.printf "@{<bold>fs@}: %s -- %s\n" (Plan.layout p1)
              (Plan.layout p2))
          fs
      in
      (* let fs = List.map (map2 (parallel_interleaving_to_trace env)) fs in *)
      (* let check_include = *)
      (*   check_regex_include env (fun (_, prop) -> *)
      (*       let p = smart_add_to bprop prop in *)
      (*       (\* let () = Printf.printf "CheckSet: %s\n" (layout_prop p) in *\) *)
      (*       Prover.check_sat_bool (smart_add_to bprop prop)) *)
      (* in *)
      let goals =
        List.concat_map
          (fun (f11, f12) ->
            let posts = Plan.insert f12 post in
            (* let old_cur = EffEvent { op; vs; phi = smart_add_to phi' phi } in *)
            let f11' = dep_elem :: f11 in
            let pres =
              List.map (Plan.divide_by_elem dep_elem) @@ Plan.insert f11' pre
            in
            let pres =
              List.concat_map
                (fun (pre1, dep_elem', pre2) ->
                  let pre1s = Plan.merge_plan history_plan pre1 in
                  List.map (fun pre1 -> (pre1, dep_elem', pre2)) pre1s)
                pres
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
      let () = List.iter layout_syn_back_judgement goals in
      let goals = List.map (fun (gamma, reg) -> (args, gamma, reg)) goals in
      goals
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
    let goals = List.concat_map handle rules in
    (* let () = if String.equal op "eCoffeeMakerReady" then _die [%here] in *)
    let abd_and_backtract (args, gamma, mid_plan) =
      let () =
        Pp.printf "@{<bold>Before Abduction@}: ";
        layout_syn_back_judgement (gamma, mid_plan)
      in
      let* gamma' = Abduction.abduction_mid_goal env gamma mid_plan args in
      let () =
        Pp.printf "@{<bold>After Abduction@}: ";
        layout_syn_back_judgement (gamma', mid_plan)
      in
      let goal = optimize_back_goal (gamma', mid_plan) in
      let () =
        Pp.printf "@{<bold>After Opt@}: ";
        layout_syn_back_judgement goal
      in
      backward env goal
    in
    (* let goals = List.map optimize_back_goal goals in *)
    backtrack abd_and_backtract goals

let quantifier_elimination (qvs, gprop, qv, local_qvs, prop) =
  let () = Printf.printf "remove qv: %s\n" (layout_qv qv) in
  let () = Printf.printf "qvs: %s\n" (layout_qvs qvs) in
  let () = Printf.printf "prop: %s\n" (layout_prop prop) in
  (* let check_valid_feature lit = *)
  (*   let aux prop = *)
  (*     Prover.check_valid (smart_forall (qv :: qvs) @@ smart_implies gprop prop) *)
  (*   in *)
  (*   (not (aux @@ lit_to_prop lit)) && not (aux @@ Not (lit_to_prop lit)) *)
  (* in *)
  (* let check_valid_pre prop = *)
  (*   not *)
  (*     (Prover.check_valid *)
  (*        (smart_forall (qv :: qvs) @@ smart_implies gprop (Not prop))) *)
  (* in *)
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

let instantiation_var (gamma : Gamma.gamma) vs { bvs; bprop } =
  let cs = get_consts bprop in
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
  (* let check_valid_feature lit = *)
  (*   let aux prop = *)
  (*     Prover.check_valid *)
  (*       (smart_forall gamma.bvs @@ smart_implies gamma.bprop prop) *)
  (*   in *)
  (*   (not (aux @@ lit_to_prop lit)) && not (aux @@ Not (lit_to_prop lit)) *)
  (* in *)
  let check_valid_pre prop =
    not
      (Prover.check_valid
         (smart_forall gamma.bvs @@ smart_implies gamma.bprop (Not prop)))
  in
  let check_valid abd =
    let p =
      smart_forall (gamma.bvs @ vs)
      @@ smart_exists bvs
      @@ smart_implies (smart_add_to abd gamma.bprop) bprop
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
      let zprop' = smart_or fvs in
      let gamma =
        Gamma.{ bvs = gamma.bvs @ vs; bprop = smart_add_to zprop' gamma.bprop }
      in
      (gamma, zprop')

let instantiation env goal =
  let get_fvargs gamma args qvs =
    let args' = List.filter (Gamma.not_mem gamma) args in
    let qvs' = List.filter (tv_not_mem args) qvs in
    let () =
      Printf.printf
        "get_fvargs:::\n\
         gamma: %s $$$ vargs: %s $$$ qvs: %s\n\
         ==>args: %s $$$ qvs: %s\n"
        (layout_qvs gamma.bvs) (layout_qvs args) (layout_qvs qvs)
        (layout_qvs args') (layout_qvs qvs')
    in
    (args', qvs')
  in
  let rec handle gamma (gamma', plan) =
    let () =
      Printf.printf "Gamma: %s\n" (Gamma.layout gamma);
      layout_syn_plan_judgement goal
    in
    match plan with
    | [] -> if 0 == List.length gamma'.bvs then mk_term_tt else _die [%here]
    | PlanAct { op; args } :: plan ->
        let fargs, qvs = get_fvargs gamma args gamma'.bvs in
        let gamma' = { bvs = qvs; bprop = gamma'.bprop } in
        let gamma, prop' = instantiation_var gamma fargs gamma' in
        let e = handle gamma (gamma', plan) in
        if is_gen env op then
          (* let e = *)
          (*   mk_term_assertP prop' *)
          (*   @@ mk_term_gen env op (List.map (fun x -> VVar x) args) e *)
          (* in *)
          mk_term_assume fargs prop'
          @@ mk_term_gen env op (List.map (fun x -> VVar x) args) e
        else
          let args' =
            List.map
              (fun x ->
                if name_in_qvs x.x fargs then x
                else (Rename.unique "tmp") #: x.ty)
              args
          in
          let ps =
            List.filter_map (fun (x, y) ->
                if String.equal x.x y.x then None
                else
                  let lit = mk_lit_eq_lit x.ty (AVar x) (AVar y) in
                  Some (lit_to_prop lit))
            @@ _safe_combine [%here] args' args
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
  let* gamma, plan = deductive_synthesis_reg env goal in
  let () = Printf.printf "Result: %s\n" (Plan.layout_plan plan) in
  let term = instantiation env (gamma, plan) in
  Some term
(* Some (reverse_instantiation env res) *)

let syn_one env =
  match synthesize env @@ mk_synthesis_goal env with
  | None -> _die_with [%here] "synthesis fails"
  | Some term -> term

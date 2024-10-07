open Language
open AutomataLibrary

type sregex = Nt.t sevent raw_regex

type 'a goal_env = {
  qvs : (Nt.t, string) typed list;
  global_prop : Nt.t prop;
  reg : 'a;
}

let map_goal f { qvs; global_prop; reg } = { qvs; global_prop; reg = f reg }

open Zdatatype

type cur = { op : string; vs : (Nt.t, string) typed list; phi : Nt.t prop }
[@@deriving sexp, show, eq, ord]

let normalize_regex (rawreg : DesymFA.raw_regex) =
  (* let () = Printf.printf "Desym Reg: %s\n" (layout_desym_regex goal.reg) in *)
  (* let () = *)
  (*   Printf.printf "Desym Raw Reg%s\n" (DesymFA.layout_raw_regex rawreg) *)
  (* in *)
  (* let () = Printf.printf "%s\n" (DesymFA.layout_dfa fa) in *)
  let open DesymFA in
  dfa_to_reg @@ minimize @@ compile_raw_regex_to_dfa rawreg

let is_empty_raw_regex = function Empty -> true | _ -> false

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
  (* let reg = SFA.regex_to_raw reg in *)
  goal
(* (rctx, reg) *)

let layout_planing_judgement goal f =
  let ctx_str =
    spf "%s | %s" (layout_qvs goal.qvs) (layout_prop goal.global_prop)
  in
  Printf.printf "%s|- %s\n\n" ctx_str (f goal.reg)

let layout_syn_reg_judgement goal =
  layout_planing_judgement goal SFA.layout_raw_regex

let layout_syn_trace_judgement goal =
  layout_planing_judgement goal SFA.omit_layout_symbolic_trace

let layout_syn_back_judgement goal =
  (* let open SFA in *)
  layout_planing_judgement goal (fun (pre, { op; vs; phi }, post) ->
      spf "back [%s] %s [%s]"
        (SFA.omit_layout_symbolic_trace pre)
        (layout_se (EffEvent { op; vs; phi }))
        (SFA.omit_layout_symbolic_trace post))

let layout_syn_tmp_judgement goal =
  (* let open SFA in *)
  layout_planing_judgement goal (fun (pre, se, post) ->
      spf "tmp [%s] %s [%s]"
        (SFA.omit_layout_symbolic_trace pre)
        (layout_se se)
        (SFA.omit_layout_symbolic_trace post))

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

[@@@warning "-27"]
[@@@warning "-26"]

let backtrack f l =
  List.fold_left
    (fun res x -> match res with Some _ -> res | None -> f x)
    None l

let raw_reg_map f reg =
  let rec aux = function
    | Empty -> Empty
    | Eps -> Eps
    | MultiChar cs -> MultiChar (f cs)
    | Alt (r1, r2) -> Alt (aux r1, aux r2)
    | Inters (r1, r2) -> Inters (aux r1, aux r2)
    | Comple (cs, r2) -> Comple (f cs, aux r2)
    | Seq rs -> Seq (List.map aux rs)
    | Star r -> Star (aux r)
  in
  aux reg

let unify_se cs =
  let open SFA in
  let m =
    CharSet.fold
      (fun se m ->
        match se with
        | GuardEvent _ -> _die [%here]
        | EffEvent { op; vs; phi } ->
            StrMap.update op
              (function
                | None -> Some (vs, phi)
                | Some (vs', phi') -> Some (vs', smart_add_to phi phi'))
              m)
      cs StrMap.empty
  in
  StrMap.fold
    (fun op (vs, phi) -> CharSet.add (EffEvent { op; vs; phi }))
    m CharSet.empty

let rec unify_sregex reg =
  match reg with
  | Empty | Eps -> reg
  | MultiChar cs -> MultiChar (unify_se cs)
  | Alt (r1, r2) -> Alt (unify_sregex r1, unify_sregex r2)
  | Inters (r1, r2) -> Inters (unify_sregex r1, unify_sregex r2)
  | Comple (cs, r2) -> Comple (unify_se cs, unify_sregex r2)
  | Seq rs -> Seq (List.map unify_sregex rs)
  | Star r -> Star (unify_sregex r)

let divide_charset_by_op cs =
  let open DesymFA in
  let m =
    CharSet.fold
      (fun (op, id) ->
        StrMap.update op (function
          | None -> Some (StateSet.singleton id)
          | Some s -> Some (StateSet.add id s)))
      cs StrMap.empty
  in
  let add_op op s =
    StateSet.fold (fun id -> CharSet.add (op, id)) s CharSet.empty
  in
  StrMap.fold (fun op m res -> add_op op m :: res) m []

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
        let reg = normalize_regex @@ regex_to_raw reg in
        if is_empty_raw_regex reg then []
        else
          let unf =
            DesymFA.raw_regex_to_union_normal_form divide_charset_by_op reg
          in
          let unf = List.map (List.map (raw_reg_map backward_maping)) unf in
          let unf =
            List.map
              (fun l -> { qvs; global_prop; reg = unify_sregex @@ seq l })
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

let subst_cty (name, lit) { nt; phi } =
  { nt; phi = subst_prop_instance name lit phi }

let subst_raw_regex f r =
  let rec aux r =
    match r with
    | Empty | Eps -> r
    | MultiChar cs -> MultiChar (f cs)
    | Alt (r1, r2) -> Alt (aux r1, aux r2)
    | Inters (r1, r2) -> Inters (aux r1, aux r2)
    | Seq l -> Seq (List.map aux l)
    | Star r -> Star (aux r)
    | Comple (cs, r) -> Comple (f cs, aux r)
  in
  aux r

let subst_raw_sregex (name, lit) r =
  subst_raw_regex (SFA.CharSet.map (subst_sevent_instance name lit)) r

let subst_haft (name, lit) t =
  let rec aux = function
    | RtyBase cty -> RtyBase (subst_cty (name, lit) cty)
    | RtyHAF { history; adding; future } ->
        let history, adding, future =
          map3 (subst_raw_sregex (name, lit)) (history, adding, future)
        in
        RtyHAF { history; adding; future }
    | RtyHAParallel { history; adding_se; parallel } ->
        let history = subst_raw_sregex (name, lit) history in
        let adding_se = subst_sevent_instance name lit adding_se in
        let parallel = List.map (subst_sevent_instance name lit) parallel in
        RtyHAParallel { history; adding_se; parallel }
    | RtyArr { arg; argcty; retrty } ->
        RtyArr
          { arg; argcty = subst_cty (name, lit) argcty; retrty = aux retrty }
    | RtyInter (t1, t2) -> RtyInter (aux t1, aux t2)
  in
  aux t

let rec fresh_haft t =
  match t with
  | RtyBase _ | RtyHAF _ | RtyHAParallel _ -> t
  | RtyArr { arg; argcty; retrty } ->
      let arg' = Rename.unique arg in
      let retrty = subst_haft (arg, AVar arg' #: argcty.nt) retrty in
      RtyArr { arg = arg'; argcty; retrty }
  | RtyInter (t1, t2) -> RtyInter (fresh_haft t1, fresh_haft t2)

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

let smart_forall qvs prop =
  List.fold_right (fun qv body -> Forall { qv; body }) qvs prop

let smart_exists qvs prop =
  List.fold_right (fun qv body -> Exists { qv; body }) qvs prop

let rec get_consts_from_lit = function
  | AAppOp (_, args) -> List.concat_map get_consts_from_typed_lit args
  | AC c -> [ c ]
  | _ -> []

and get_consts_from_typed_lit lit = get_consts_from_lit lit.x

let get_consts prop =
  let lits = get_lits prop in
  let cs = List.concat_map get_consts_from_lit lits in
  List.slow_rm_dup equal_constant cs

let lit_to_nt = function
  | AC c -> constant_to_nt c
  | AAppOp (op, args) -> snd @@ Nt.destruct_arr_tp op.ty
  | AVar x -> x.ty
  | _ -> _die [%here]

let lit_to_prop lit = Lit lit #: (lit_to_nt lit)

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
    let fvtab = build_euf lits in
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

let parallel_interleaving l =
  let l = None :: List.map (fun x -> Some x) l in
  let l = List.permutation l in
  let rec aux pre = function
    | [] -> (pre, [])
    | None :: res -> (pre, List.filter_map (fun x -> x) res)
    | Some x :: res -> aux (pre @ [ x ]) res
  in
  List.map (aux []) l

let mk_raw_all env =
  let l =
    List.map (fun x -> EffEvent { op = x.x; vs = x.ty; phi = mk_true })
    @@ ctx_to_list env.event_tyctx
  in
  if List.length l == 0 then _die [%here] else MultiChar (SFA.CharSet.of_list l)

let parallel_interleaving_to_trace env l =
  let all = Star (mk_raw_all env) in
  all
  :: List.concat_map (fun r -> [ MultiChar (SFA.CharSet.singleton r); all ]) l

let trace_to_raw_regex = function
  | [] -> Eps
  | _ as l -> List.left_reduce [%here] SFA.alt l

let inter_trace env { qvs; global_prop; reg = tr1, tr2 } =
  let r1, r2 = map2 trace_to_raw_regex (tr1, tr2) in
  let reg = Inters (r1, r2) in
  normalize_goal env { qvs; global_prop; reg }

let single_insert_into_trace se trace =
  let rec aux (res, pre) = function
    | [] -> res
    | Star r :: rest ->
        aux
          ( ( pre @ [ Star r ],
              [ MultiChar (SFA.CharSet.singleton se) ],
              [ Star r ] @ rest )
            :: res,
            pre @ [ Star r ] )
          rest
    | MultiChar cs :: rest -> aux (res, pre @ [ MultiChar cs ]) rest
    | _ -> _die [%here]
  in
  aux ([], []) trace

let rec insert_into_trace ses trace =
  match ses with
  | [] -> [ trace ]
  | [ se ] ->
      List.map (fun (a, b, c) -> a @ b @ c) @@ single_insert_into_trace se trace
  | se :: rest ->
      let l = single_insert_into_trace se trace in
      List.concat_map
        (fun (a, b, trace) ->
          let trace' = insert_into_trace rest trace in
          List.map (fun c -> a @ b @ c) trace')
        l

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

let raw_regex_to_trace = function Seq l -> l | _ -> _die [%here]

let charset_to_se loc s =
  let open SFA in
  match List.of_seq @@ CharSet.to_seq s with [ x ] -> x | _ -> _die loc

let se_to_raw_regex se = MultiChar (SFA.CharSet.singleton se)

let rec deductive_synthesis_reg env goal : SFA.raw_regex goal_env option =
  let goals = normalize_goal env goal in
  let res = List.filter_map (deductive_synthesis_trace env) goals in
  match res with [] -> None | g :: _ -> Some g

and deductive_synthesis_trace env goal : SFA.raw_regex goal_env option =
  let goal = map_goal raw_regex_to_trace goal in
  let () = layout_syn_trace_judgement goal in
  let subgoals =
    List.filter_map
      (function MultiChar s -> Some (charset_to_se [%here] s) | _ -> None)
      goal.reg
  in
  let handle goal subgoal =
    (* let () = Printf.printf "this step\n" in *)
    (* let () = layout_syn_trace_judgement goal in *)
    let pre, post = trace_divide_by_se subgoal goal.reg in
    let cur = se_to_cur [%here] subgoal in
    let goal = map_goal (fun _ -> (pre, cur, post)) goal in
    let* goal = backward env goal in
    let goal =
      map_goal
        (fun (pre, cur, post) -> pre @ [ se_to_raw_regex cur ] @ post)
        goal
    in
    let () = Printf.printf "next step\n" in
    let () = layout_syn_trace_judgement goal in
    Some goal
  in
  let* res =
    List.fold_left
      (fun goal subgoal ->
        match goal with
        | None -> _die [%here]
        | Some goal -> handle goal subgoal)
      (Some goal) subgoals
  in
  Some (map_goal (fun trs -> SFA.seq trs) goal)

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

and backward env ({ qvs; global_prop; reg = pre, cur, post } as goal) =
  let () = layout_syn_back_judgement goal in
  let { op; vs; phi } = cur in
  match get_opt env.gen_ctx op with
  | None -> _die [%here]
  | Some true ->
      Some { qvs; global_prop; reg = (pre, EffEvent { op; vs; phi }, post) }
  | Some false ->
      let handle (se, haft) =
        let () =
          Printf.printf "handle se: %s haft: %s\n" (layout_se se)
            (layout_haft SFA.layout_raw_regex haft)
        in
        let args, retrty = destruct_haft [%here] haft in
        let history, adding_se, p = destruct_hap [%here] retrty in
        let op, _, phi' = _get_sevent_fields [%here] se in
        let* gprop = abduction goal args (vs, phi, phi') in
        let args = List.map (fun x -> x.x #: x.ty.nt) args in
        let qvs = qvs @ args in
        let global_prop = smart_add_to gprop global_prop in
        let fs = parallel_interleaving p in
        (* let fs = List.map (map2 (parallel_interleaving_to_trace env)) fs in *)
        let goals =
          List.concat_map
            (fun (f11, f12) ->
              let posts = insert_into_trace f12 post in
              let old_cur = EffEvent { op; vs; phi = smart_add_to phi' phi } in
              let f11' = adding_se :: f11 in
              let pres =
                List.map (trace_divide_by_se adding_se)
                @@ insert_into_trace f11' pre
              in
              let goals =
                List.map (fun ((pre1, pre2), post) ->
                    {
                      qvs;
                      global_prop;
                      reg =
                        ( pre1,
                          se_to_cur [%here] adding_se,
                          pre2
                          @ [ MultiChar (SFA.CharSet.singleton old_cur) ]
                          @ post );
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
      backtrack (backward env) goals

let synthesize env goal =
  let res = deductive_synthesis_reg env goal in
  res

let test env =
  let _ = synthesize env @@ mk_synthesis_goal env in
  ()

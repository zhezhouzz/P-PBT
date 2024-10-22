open Language

type sregex = Nt.t sevent raw_regex
type 'a sgoal = Gamma.gamma * 'a

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

let layout_plan_mid (pre, cur, post) =
  let open Plan in
  spf "back [%s] %s [%s]" (omit_layout pre) (layout_elem cur) (omit_layout post)

let layout_syn_back_judgement (gamma, (pre, cur, post)) =
  layout_planing_judgement gamma (layout_plan_mid (pre, cur, post))

open Zdatatype

let rec filter_rule_by_future op = function
  | RtyHAParallel { parallel; adding_se; history } -> (
      (* HACK: assume each op only has one sevent. *)
      let ses, parallel' =
        List.partition
          (fun se -> String.equal op (_get_sevent_name se))
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
  | RtyGArr { arg; argnt; retrty } ->
      let* se, retrty = filter_rule_by_future op retrty in
      Some (se, RtyGArr { arg; argnt; retrty })
  | _ -> _die [%here]

let select_rule_by_future env op =
  List.concat_map
    (fun x ->
      let l = haft_to_triple x.ty in
      let l = List.filter_map (filter_rule_by_future op) l in
      l)
    (List.map (fun x -> x.x #: (fresh_haft x.ty))
    @@ ctx_to_list env.event_rtyctx)

let charset_to_se loc s =
  let open SFA in
  match List.of_seq @@ CharSet.to_seq s with [ x ] -> x | _ -> _die loc

let clearn_trace trace =
  List.filter_map
    (function
      | MultiChar c -> Some (charset_to_se [%here] c)
      | Star _ -> None
      | _ -> _die [%here])
    trace

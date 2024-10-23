open Language

type sregex = Nt.t sevent raw_regex
type 'a sgoal = Gamma.gamma * 'a

open Gamma
open Zdatatype

let simp_print_gamma_judgement { bvs; bprop } =
  Pp.printf "@{<bold>@{<red>Γ:@} %s |@} %s\n"
    (List.split_by_comma _get_x bvs)
    (layout_prop bprop)

let print_gamma_judgement { bvs; bprop } =
  Pp.printf "@{<bold>@{<red>Γ:@}@} %s | %s\n" (layout_qvs bvs)
    (layout_prop bprop)

let simp_print_mid_judgement (pre, cur, post) =
  let open Plan in
  Pp.printf "@{<bold>[@} %s @{<bold>]@}\n %s\n@{<bold>[@} %s @{<bold>]@}\n\n"
    (omit_layout pre) (layout_elem cur) (omit_layout post)

let simp_print_back_judgement (gamma, plan) =
  Pp.printf "@{<bold>@{<yellow>Backword:@}@}\n";
  simp_print_gamma_judgement gamma;
  simp_print_mid_judgement plan

let simp_print_goal_judgement (gamma, plan) =
  simp_print_gamma_judgement gamma;
  simp_print_mid_judgement plan

let simp_print_forward_judgement (gamma, plan) =
  Pp.printf "@{<bold>@{<yellow>Forward:@}@}\n";
  simp_print_gamma_judgement gamma;
  simp_print_mid_judgement plan

let simp_print_syn_judgement (gamma, reg) =
  Pp.printf "@{<bold>@{<yellow>Synthesis:@}@}\n";
  simp_print_gamma_judgement gamma;
  Pp.printf "%s\n" (Plan.omit_layout reg)

let simp_print_opt_plan_judgement (gamma1, plan1) m (gamma2, plan2) =
  Pp.printf "@{<bold>@{<yellow>Optimize:@}@}\n";
  simp_print_gamma_judgement gamma1;
  simp_print_mid_judgement plan1;
  Pp.printf "@{<yellow>Map:@} %s\n"
    (List.split_by "; " (fun (x, y) -> spf "%s --> %s" x y.x) m);
  simp_print_gamma_judgement gamma2;
  simp_print_mid_judgement plan2

let simp_print_instantiation gamma (gamma', plan) =
  Pp.printf "@{<bold>@{<yellow>Instantiation:@} With@}\n";
  simp_print_gamma_judgement gamma;
  Pp.printf "@{<yellow>Instantiation:@}\n";
  simp_print_gamma_judgement gamma';
  Pp.printf "%s\n" @@ Plan.omit_layout plan

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
          (* let () = *)
          (*   Printf.printf "parallel %s --> %s\n" *)
          (*     (List.split_by_comma layout_se parallel) *)
          (*     (List.split_by_comma layout_se parallel') *)
          (* in *)
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

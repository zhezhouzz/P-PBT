open Language
open AutomataLibrary

type sregex = Nt.t sevent raw_regex

type 'a goal_env = {
  qvs : (Nt.t, string) typed list;
  global_prop : Nt.t prop;
  reg : 'a raw_regex;
}

open Zdatatype

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

let layout_planing_judgement goal str =
  let ctx_str =
    spf "%s | %s" (layout_qvs goal.qvs) (layout_prop goal.global_prop)
  in
  Printf.printf "%s|- %s\n\n" ctx_str str

let layout_syn_reg_judgement goal reg =
  layout_planing_judgement goal (SFA.layout_raw_regex reg)

let layout_syn_trace_judgement goal trace =
  layout_planing_judgement goal (SFA.omit_layout_symbolic_trace trace)

let layout_syn_back_judgement goal (h, a, f) =
  let open SFA in
  layout_planing_judgement goal
    (spf "back [ %s ]%s[ %s ]"
       (omit_layout_symbolic_trace h)
       (layout_raw_regex (MultiChar a))
       (omit_layout_symbolic_trace f))

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
          let unf = List.map (fun l -> { qvs; global_prop; reg = seq l }) unf in
          unf)
      goals
  in
  goals

let rec deductive_synthesis_reg env goal : DesymFA.raw_regex option =
  let goals = normalize_goal env goal in
  let res = List.filter_map (deductive_synthesis_trace env) goals in
  match res with [] -> None | l -> Some (DesymFA.seq l)

and deductive_synthesis_trace env goal : DesymFA.raw_regex option =
  let trace = match goal.reg with Seq l -> l | _ -> _die [%here] in
  let () = layout_syn_trace_judgement goal trace in
  let rec aux res (pre, post) =
    match post with
    | [] -> res
    | MultiChar cur :: post ->
        aux ((pre, cur, post) :: res) (pre @ [ MultiChar cur ], post)
    | x :: post -> aux res (pre @ [ x ], post)
  in
  let tasks = aux [] ([], trace) in
  backtrack (backward env goal) tasks

and backward env ({ qvs; global_prop; _ } as goal) (pre, cur, post) =
  let () = layout_syn_back_judgement goal (pre, cur, post) in
  None

let synthesize env goal =
  let res = deductive_synthesis_reg env goal in
  res

let test env =
  let _ = synthesize env @@ mk_synthesis_goal env in
  ()

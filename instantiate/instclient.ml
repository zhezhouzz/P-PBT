open Language
open Zdatatype

type rexpr = (Nt.t, Nt.t sevent) regex_expr

(* HACK: we assume all axioms have the same quantified varaibles *)
let unify_multiple_qvs qvss =
  let res =
    List.fold_left
      (fun qvs qvs' ->
        match qvs with
        | None -> Some qvs'
        | Some qvs ->
            if
              List.eq
                (fun a b -> String.equal a.x b.x && Nt.equal_nt a.ty b.ty)
                qvs qvs'
            then Some qvs
            else None)
      None qvss
  in
  match res with
  | None ->
      _failatwith [%here] "the quantified varaibles of axioms should be unified"
  | Some res -> res

let destruct_universal_qgrex =
  let rec aux = function
    | RExpr e ->
        let qvs, body = aux_expr e in
        (qvs, body)
    | e -> ([], e)
  and aux_expr = function
    | QFRegex { qv = { x; ty = RForall nt }; body } ->
        let qvs, body = aux body in
        ((x #: nt) :: qvs, body)
    | QFRegex _ -> _die [%here]
    | e -> ([], RExpr e)
  in
  aux_expr

let mk_complement = function
  | RExpr (RRegex (Extension (ComplementA r))) -> r
  | Extension (ComplementA r) -> r
  | _ as reg -> Extension (ComplementA reg)

let mk_last_violate spec_tyctx reg =
  let none_reqs =
    List.filter_map
      (fun x ->
        match x.ty with Resp -> Some x.x | Hidden -> Some x.x | Req -> None)
      (ctx_to_list spec_tyctx.event_kindctx)
  in
  let postfix =
    SyntaxSugar
      (CtxOp
         {
           op_names = none_reqs;
           body = SeqA (Extension AnyA, StarA (Extension AnyA));
         })
  in
  (* let () = Printf.printf "%s\n" (layout_sexp_regex reg) in *)
  (* let () = failwith "die" in *)
  (* SeqA (reg, postfix) *)
  LandA (SeqA (reg, postfix), mk_complement reg)

(* let regspec_to_sfa mode ctx m = *)
(*   let vs, reg = *)
(*     Desymbolic.(desymbolic_regspec mode ctx) *)
(*       (fun (_, prop) -> Prover.check_sat_bool prop) *)
(*       m *)
(*   in *)
(*   (\* let () = Printf.printf " zz?: %s\n" @@ layout_symbolic_regex reg in *\) *)
(*   let module DFA = DesymFA in *)
(*   let f (global_prop, bmap, reg) = *)
(*     let fa = DFA.compile_regex_to_dfa reg in *)
(*     (\* let () = Pp.printf "\n@{<bold>To DFA:@}\n%s\n" (DFA.layout_dfa fa) in *\) *)
(*     let sfa = SFA.from_desym_dfa bmap fa in *)
(*     (\* let () = Pp.printf "\n@{<bold>Back To SFA:@}\n%s\n" (SFA.layout_dfa sfa) in *\) *)
(*     (global_prop, sfa) *)
(*   in *)
(*   (vs, List.map f reg) *)

let to_sfa_client ctx client =
  let _, axiom =
    Desymbolic.regspec_to_sfa UnionFA ctx.event_tyctx
      (get_qvs_from_world client.axiom_world, client.axiom)
  in
  let _, violation =
    Desymbolic.regspec_to_sfa OriginalFA ctx.event_tyctx
      (get_qvs_from_world client.violation_world, client.violation)
  in
  { client with axiom; violation }

let print_qstrsfa (prop, sfa) =
  let () = Printf.printf "World Prop: %s\n" (layout_prop prop) in
  (* let () = *)
  (*   Printf.printf "%i is mem of dfa?: %b\n" 6 (StateMap.mem 6 sfa.SFA.next) *)
  (* in *)
  (* let _ = SFA.display_dfa sfa in *)
  let _ = StrAutomata.display_dfa @@ symbolic_dfa_to_event_name_dfa sfa in
  (* let () = *)
  (*   Printf.printf "%i is mem of dfa?: %b\n" 6 *)
  (*     (StateMap.mem 6 (symbolic_dfa_to_event_name_dfa sfa).next) *)
  (* in *)
  ()

let print_transsfa (prop, sfa) =
  let () = Printf.printf "World Prop: %s\n" (layout_prop prop) in
  let () = Printf.printf "%s\n" (SFA.layout_dfa sfa) in
  (* let () = *)
  (*   Printf.printf "%i is mem of dfa?: %b\n" 6 (StateMap.mem 6 sfa.SFA.next) *)
  (* in *)
  (* let _ = SFA.display_dfa sfa in *)
  (* let _ = StrAutomata.display_dfa @@ symbolic_dfa_to_event_name_dfa sfa in *)
  (* let () = *)
  (*   Printf.printf "%i is mem of dfa?: %b\n" 6 *)
  (*     (StateMap.mem 6 (symbolic_dfa_to_event_name_dfa sfa).next) *)
  (* in *)
  ()

let print_qsfa (prop, sfa) =
  let () = Printf.printf "World Prop: %s\n" (layout_prop prop) in
  (* let () = Printf.printf "%s\n" (SFA.layout_dfa sfa) in *)
  (* let () = *)
  (*   Printf.printf "%i is mem of dfa?: %b\n" 6 (StateMap.mem 6 sfa.SFA.next) *)
  (* in *)
  let _ = SFA.display_dfa sfa in
  (* let _ = StrAutomata.display_dfa @@ symbolic_dfa_to_event_name_dfa sfa in *)
  (* let () = *)
  (*   Printf.printf "%i is mem of dfa?: %b\n" 6 *)
  (*     (StateMap.mem 6 (symbolic_dfa_to_event_name_dfa sfa).next) *)
  (* in *)
  ()

let mk_clients_ctx (spec_tyctx : spec_tyctx) (rexpr_ctx : rexpr ctx)
    (code : Nt.t item list) =
  add_to_rights emp
  @@ List.filter_map
       (function
         | MClient
             {
               client_name;
               event_scope;
               axioms;
               type_configs;
               violation;
               step_bound;
             } ->
             let spec_tyctx =
               add_config_to_spec_tyctx spec_tyctx type_configs
             in
             let limit_with_scope body =
               SyntaxSugar (CtxOp { op_names = event_scope; body })
             in
             let axioms = List.map (_get_force [%here] rexpr_ctx) axioms in
             let qvss, axioms =
               List.split @@ List.map destruct_universal_qgrex axioms
             in
             let axiom_qvs = unify_multiple_qvs qvss in
             let axiom_world = mk_forall_world axiom_qvs in
             let axiom = _smart_inter [%here] axioms in
             let violation_qvs, violation =
               destruct_universal_qgrex (_get_force [%here] rexpr_ctx violation)
             in
             let axiom' =
               List.fold_right
                 (fun (x, y) res -> subst_regex res x.x (RVar y))
                 (_safe_combine [%here] axiom_qvs violation_qvs)
                 axiom
             in
             let violation_world = mk_exists_world violation_qvs in
             let () =
               List.iter print_qstrsfa @@ snd
               @@ Desymbolic.regspec_to_sfa OriginalFA spec_tyctx.event_tyctx
                    ( get_qvs_from_world violation_world,
                      limit_with_scope violation )
             in
             let violation =
               LandA (axiom', mk_last_violate spec_tyctx violation)
             in
             Some
               client_name
               #: {
                    spec_tyctx;
                    client_name;
                    event_scope;
                    type_configs;
                    axiom_world;
                    axiom = limit_with_scope axiom;
                    violation_world;
                    violation = limit_with_scope violation;
                    step_bound;
                  }
         | _ -> None)
       code

let layout_event_kindctx =
  ctx_to_list
  #> (List.split_by_comma (fun { x; ty = kind } ->
          spf "%s:%s" x @@ layout_event_kind kind))

let layout_basic_ctx ctx =
  let res =
    spf "event_kindctx:\n%s\n"
    @@ layout_event_kindctx ctx.spec_tyctx.event_kindctx
  in
  let res = spf "%sstep_bound:%i\n" res ctx.step_bound in
  res

let layout_regex_client client =
  let res = layout_basic_ctx client in
  let axiom_str =
    spf "%s\n\t%s"
      (layout_world client.axiom_world)
      (layout_symbolic_regex client.axiom)
  in
  let violation_str =
    spf "%s.\n\t%s"
      (layout_world client.violation_world)
      (layout_symbolic_regex client.violation)
  in
  spf "Client %s:\n%s\n%s\n%s\nstep bound: %i\n" res client.client_name
    axiom_str violation_str client.step_bound

let print_strsfa_client client =
  let () =
    Printf.printf "Client %s\n%s\n" client.client_name (layout_basic_ctx client)
  in
  let () = Printf.printf "%s\n" (layout_world client.axiom_world) in
  let () = List.iter print_qstrsfa client.axiom in
  let () = Printf.printf "%s\n" (layout_world client.violation_world) in
  let () = List.iter print_qstrsfa client.violation in
  let () = Printf.printf "step bound: %i\n" client.step_bound in
  ()

let print_strsfa_client_violation client =
  let () =
    Printf.printf "Client %s\n%s\n" client.client_name (layout_basic_ctx client)
  in
  let () = Printf.printf "%s\n" (layout_world client.violation_world) in
  let () = List.iter print_qstrsfa client.violation in
  ()

let print_sfa_client_violation client =
  let () =
    Printf.printf "Client %s\n%s\n" client.client_name (layout_basic_ctx client)
  in
  let () = Printf.printf "%s\n" (layout_world client.violation_world) in
  let () = List.iter print_qsfa client.violation in
  ()

let print_transsfa_client_violation client =
  let () =
    Printf.printf "Client %s\n%s\n" client.client_name (layout_basic_ctx client)
  in
  let () = Printf.printf "%s\n" (layout_world client.violation_world) in
  let () = List.iter print_transsfa client.violation in
  ()

let print_sfa_client client =
  let () =
    Printf.printf "Client %s\n%s\n" client.client_name (layout_basic_ctx client)
  in
  let () = Printf.printf "%s\n" (layout_world client.axiom_world) in
  let () = List.iter print_qsfa client.axiom in
  let () = Printf.printf "%s\n" (layout_world client.violation_world) in
  let () = List.iter print_qsfa client.violation in
  let () = Printf.printf "step bound: %i\n" client.step_bound in
  ()

let layout_qautomata (world_prop, dfa) =
  let res = spf "world_prop:%s\n" @@ layout_prop world_prop in
  let res = spf "%s%s" res @@ SFA.layout_dfa dfa in
  res

let inst_client spec_tyctx code =
  let rexpr_ctx = Instspec.eta_reduction_items emp code in
  let client_ctx = mk_clients_ctx spec_tyctx rexpr_ctx code in
  let client_ctx =
    map_ctx
      (fun client ->
        let client = to_sfa_client spec_tyctx client in
        (* let () = print_strsfa_client client in *)
        client)
      client_ctx
  in
  client_ctx

(* let regex_expr_to_machine_opt (r : rexpr) : *)
(*     (Nt.t, Nt.t sevent) regex machine option = *)
(*   let rec aux binding r = *)
(*     (\* let () = Printf.printf "To: %s\n" (layout_raw_regex (RExpr r)) in *\) *)
(*     (\* let () = Printf.printf "to: %s\n" @@ layout_symbolic_regex (RExpr r) in *\) *)
(*     match r with *)
(*     | QFRegex { qv; body } -> ( *)
(*         match qv.ty with *)
(*         | RForallC c -> *)
(*             aux (binding @ [ (qv.x, Nt.Fa, c) ]) (RRegex body) *)
(*         | RExistsC c -> *)
(*             aux (binding @ [ (qv.x, Nt.Ex, c) ]) (RRegex body) *)
(*         | _ -> None) *)
(*     | RRegex (RExpr r) -> aux binding r *)
(*     | RRegex r -> Some { binding; reg = r } *)
(*     | _ -> None *)
(*   in *)
(*   aux [] r *)

(* let regex_expr_to_regspec_opt (r : rexpr) = *)
(*   let rec aux r = *)
(*     (\* let () = Printf.printf "To: %s\n" (layout_raw_regex (RExpr r)) in *\) *)
(*     (\* let () = Printf.printf "to: %s\n" @@ layout_symbolic_regex (RExpr r) in *\) *)
(*     match r with *)
(*     | QFRegex { qv; body } -> ( *)
(*         match qv.ty with *)
(*         | RForall abstract_type -> *)
(*             let* world, r = aux (RRegex body) in *)
(*             Some (WMap { qv = qv.x #: abstract_type; world }, r) *)
(*         | RExists abstract_type -> *)
(*             let* world, r = aux (RRegex body) in *)
(*             Some (WSingle { qv = qv.x #: abstract_type; world }, r) *)
(*         | _ -> None) *)
(*     | RRegex (RExpr r) -> aux r *)
(*     | RRegex r -> Some (WState, r) *)
(*     | _ -> None *)
(*   in *)
(*   let* world, reg = aux r in *)
(*   Some { world; reg } *)

(* let rename_regspec_by_event_ctx ctx { world; reg } = *)
(*   let reg = *)
(*     List.map (fun (prop, reg) -> (prop, SFA.rename_sevent ctx reg)) reg *)
(*   in *)
(*   { world; reg } *)

(* let regspecs_to_sfas m = StrMap.map regspec_to_sfa m *)

(* let machine_to_sfa mode (m : (Nt.t, Nt.t sevent) regex machine) = *)
(*   let { binding; reg } = *)
(*     Desymbolic.(desymbolic_machine mode) (fun _ -> true) m *)
(*   in *)
(*   (\* let () = Printf.printf " zz?: %s\n" @@ layout_symbolic_regex reg in *\) *)
(*   let module DFA = DesymFA in *)
(*   let f (global_prop, bmap, reg) = *)
(*     let fa = DFA.compile_regex_to_dfa reg in *)
(*     let () = Pp.printf "\n@{<bold>To DFA:@}\n%s\n" (DFA.layout_dfa fa) in *)
(*     let sfa = SFA.from_desym_dfa bmap fa in *)
(*     let () = Pp.printf "\n@{<bold>Back To SFA:@}\n%s\n" (SFA.layout_dfa sfa) in *)
(*     (global_prop, sfa) *)
(*   in *)
(*   { binding; reg = List.map f reg } *)

(* let machines_to_sfas mode *)
(*     (machines : (Nt.t, Nt.t sevent) regex machine StrMap.t) = *)
(*   StrMap.map (machine_to_sfa mode) machines *)

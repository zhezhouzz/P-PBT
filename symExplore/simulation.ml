(* open Common *)
(** Simulation:
    exists. \phi /\ sfa1 ~ forall. \phi => sfa2

    The state of sfa1 maps to a list of states of sfa2
*)

open Zzdatatype.Datatype
open Language
open SFA

(* type sim_map = (int, int list) Hashtbl.t *)

(* type ex_sfa = { *)
(*   ex_qvs : (Nt.t, string) typed list; *)
(*   ex_prop : Nt.t prop; *)
(*   dfa : SFA.dfa; *)
(* } *)

(* type fa_sfa = { *)
(*   fa_qvs : (Nt.t, string) typed list; *)
(*   fa_prop_dfas : (Nt.t prop * SFA.dfa) list; *)
(* } *)

(* type sim_ctx = { ex_sfa : ex_sfa; fa_sfa : fa_sfa } *)

(* open SFA *)

(* let get_sim_nodes (sim_ctx : sim_ctx) (state : int) = *)
(*   match Hashtbl.find_opt sim_ctx.sim_map state with *)
(*   | None -> _die_with [%here] "cannot find simulated node list" *)
(*   | Some nodes -> nodes *)

(* module StatePairMap = Map.Make (struct *)
(*   type t = int * int *)

(*   let compare (x1, y1) (x2, y2) = *)
(*     let res = Stdlib.compare x1 x2 in *)
(*     if res == 0 then Stdlib.compare y1 y2 else res *)
(* end) *)

let reachable_analysis (dfa1 : dfa) (dfa2 : dfa) =
  (* let dfa1 = normalize_dfa dfa1 in *)
  (* let dfa2 = normalize_dfa dfa2 in *)
  (* let dfa2 = symbolic_dfa_to_event_name_dfa dfa2 in *)
  (* let dfa2 = normalize_dfa dfa2 in *)
  (* map a state into a set of states *)
  let seen = Hashtbl.create 1000 in
  let _print (state, nodes) =
    spf "%i ---> [%s]" state
      (List.split_by_comma string_of_int @@ List.of_seq @@ StateSet.to_seq nodes)
  in
  let rec visit (state, nodes) =
    (* let () = Printf.printf "Visit: %s\n" @@ _print (state, nodes) in *)
    let nodes' =
      match Hashtbl.find_opt seen state with
      | None ->
          Hashtbl.add seen state StateSet.empty;
          StateSet.empty
      | Some s -> s
    in
    if StateSet.subset nodes nodes' then ()
    else
      let nodes = StateSet.union nodes nodes' in
      let () = Hashtbl.replace seen state nodes in
      let charmap1 = dfa1.next #-> state in
      let charmap2 =
        StateSet.fold
          (fun node m ->
            let m' = dfa2.next #-> node in
            let m' = CharMap.map StateSet.singleton m' in
            CharMap.union (fun _ s1 s2 -> Some (StateSet.union s1 s2)) m m')
          nodes CharMap.empty
      in
      (* let () = *)
      (*   CharMap.iter *)
      (*     (fun op nodes -> *)
      (*       Printf.printf "\twhen %s ==> [%s]\n" op *)
      (*         (List.split_by_comma string_of_int *)
      (*         @@ List.of_seq @@ StateSet.to_seq nodes)) *)
      (*     charmap2 *)
      (* in *)
      CharMap.iter
        (fun c1 d1 ->
          let s =
            CharMap.fold
              (fun c2 nodes s ->
                if
                  String.equal
                    (_get_sevent_name [%here] c2)
                    (_get_sevent_name [%here] c1)
                then StateSet.union s nodes
                else s)
              charmap2 StateSet.empty
          in
          if not (StateSet.is_empty s) then visit (d1, s))
        charmap1
  in
  let () = visit (dfa1.start, StateSet.singleton dfa2.start) in
  (* let () = *)
  (*   Hashtbl.iter *)
  (*     (fun state nodes -> Printf.printf "%s\n" @@ _print (state, nodes)) *)
  (*     seen *)
  (* in *)
  (* let () = _die [%here] in *)
  seen

let check_sat client prop =
  let prop =
    List.fold_right
      (fun qv body -> Forall { qv; body })
      (get_qvs_from_world client.axiom_world)
      prop
  in
  let prop =
    List.fold_right
      (fun qv body -> Exists { qv; body })
      (get_qvs_from_world client.violation_world)
      prop
  in
  let res = Common.sat_solver prop in
  (* let () = *)
  (*   if res then *)
  (*     Printf.printf "%s: [%s] %s\n" *)
  (*       (if res then "SAT" else "UNSAT") *)
  (*       op *)
  (*       (Language.layout_prop prop) *)
  (* in *)
  res

let sfa_cross_intersect client (prop1, dfa1) (prop2, dfa2) =
  let seen = reachable_analysis dfa1 dfa2 in
  let new_next =
    dfa_fold_transitions
      (fun (s, se, d) new_next ->
        let op, _, phi = _get_sevent_fields [%here] se in
        let s_nodes = Hashtbl.find seen s in
        let d_nodes = Hashtbl.find seen d in
        let chs =
          StateSet.fold
            (fun s_node ->
              CharMap.fold
                (fun ch d_node res ->
                  if StateSet.mem d_node d_nodes then CharSet.add ch res
                  else res)
                dfa2.next #-> s_node)
            s_nodes CharSet.empty
        in
        let props =
          CharSet.fold
            (fun se props ->
              let op', _, phi' = _get_sevent_fields [%here] se in
              if String.equal op' op then phi' :: props else props)
            chs []
        in
        let prop =
          smart_and [ smart_implies prop2 @@ smart_or props; prop1; phi ]
        in
        let is_valid = check_sat client prop in
        (* let () = *)
        (*   if is_valid then Printf.printf "%i -- [%s] -- %i???\n" s op d *)
        (* in *)
        (* let () = *)
        (*   if s == 10 then *)
        (*     Printf.printf ">>%s: [%s] %s\n" *)
        (*       (if is_valid then "SAT" else "UNSAT") *)
        (*       op *)
        (*       (Language.layout_prop prop) *)
        (* in *)
        if is_valid then dfa_next_insert s se d new_next else new_next)
      dfa1 StateMap.empty
  in
  let dfa1 = { dfa1 with next = new_next } in
  let dfa1 = SFA.minimize dfa1 in
  (* let dfa1 = SFA.unionify_sevent dfa1 in *)
  (* let () = _die [%here] in *)
  (prop1, dfa1)
(*   let op1, _, phi1 = _get_sevent_fields [%here] se1 in *)
(*   let op2, _, phi2 = _get_sevent_fields [%here] se2 in *)
(*   if not (String.equal op1 op2) then false *)
(*   else *)
(*     let prop = smart_and [ prop1; phi1; prop2; phi2 ] in *)
(*     let prop = *)
(*       List.fold_right *)
(*         (fun qv body -> Exists { qv; body }) *)
(*         (get_qvs_from_world client.axiom_world) *)
(*         prop *)
(*     in *)
(*     let prop = *)
(*       List.fold_right *)
(*         (fun qv body -> Exists { qv; body }) *)
(*         (get_qvs_from_world client.violation_world) *)
(*         prop *)
(*     in *)
(*     let res = Common.sat_solver prop in *)
(*     let () = *)
(*       Printf.printf "%s: [%s] %s\n" *)
(*         (if res then "SAT" else "UNSAT") *)
(*         op1 *)
(*         (Language.layout_prop prop) *)
(*     in *)
(*     res *)
(* in *)
(* (prop1, raw_sfa_cross_intersect check_chpair dfa1 dfa2) *)

let refine_client client =
  (* let dummy_prop = *)
  (*   List.combine *)
  (*     (get_qvs_from_world client.axiom_world) *)
  (*     (get_qvs_from_world client.violation_world) *)
  (* in *)
  (* let dummy_prop = *)
  (*   List.map (fun (x, y) -> mk_lit_eq_lit x.ty (AVar x) (AVar y)) dummy_prop *)
  (* in *)
  (* let dummy_prop = *)
  (*   List.map (fun lit -> Not (Lit lit #: Nt.Ty_bool)) dummy_prop *)
  (* in *)
  (* let dummy_prop = smart_and dummy_prop in *)
  let violation =
    List.map
      (fun ex ->
        List.fold_left
          (fun res (prop, dfa) -> sfa_cross_intersect client res (prop, dfa))
          ex client.axiom)
      client.violation
  in
  { client with violation }

let rule_out_hidden client =
  let is_hidden se =
    match
      _get_force [%here] client.spec_tyctx.event_kindctx
        (_get_sevent_name [%here] se)
    with
    | Hidden -> true
    | _ -> false
  in
  let filter dfa =
    let dfa = SFA.filter_dfa (fun se -> not (is_hidden se)) dfa in
    (* let dfa = *)
    (*   SFA.filter_dfa *)
    (*     (fun se -> *)
    (*       let op, _, prop = _get_sevent_fields [%here] se in *)
    (*       let b = Common.sat_solver prop in *)
    (*       let () = *)
    (*         Printf.printf "Check [%s] is %b: %s\n" op b (layout_prop prop) *)
    (*       in *)
    (*       b) *)
    (*     dfa *)
    (* in *)
    (* let dfa = SFA.unionify_sevent dfa in *)
    dfa
  in
  let violation =
    List.map (fun (prop, dfa) -> (prop, filter dfa)) client.violation
  in
  { client with violation }

(* let get_constraint_from_fa_sfa (sim_ctx : sim_ctx) (state : int) m = *)
(*   let nodes = get_sim_nodes sim_ctx state in *)
(*   let get_cond index node = *)
(*     let dfa = IntMap.find "die" sim_ctx.fa_sfa.dfas index in *)
(*     let prop = IntMap.find "die" sim_ctx.fa_sfa.fa_props index in *)
(*     let m = dfa.next #-> node in *)
(*     let l = *)
(*       List.map (fun (se, st) -> *)
(*           let op, _, phi = _get_sevent_fields [%here] se in *)
(*           (op, (st, phi))) *)
(*       @@ List.of_seq @@ CharMap.to_seq m *)
(*     in *)
(*     let m = *)
(*       List.fold_right *)
(*         (fun (op, (st, phi)) -> *)
(*           StrMap.update op (function *)
(*             | None -> Some (IntMap.singleton st phi) *)
(*             | Some m' -> *)
(*                 Some *)
(*                   (IntMap.update st *)
(*                      (function *)
(*                        | None -> Some phi *)
(*                        | Some phi' -> Some (smart_add_to phi phi')) *)
(*                      m'))) *)
(*         l StrMap.empty *)
(*     in *)
(*     let m = StrMap.map (IntMap.map (smart_implies prop)) m in *)
(*     m *)
(*   in *)
(*   let ll = List.mapi get_cond nodes in *)
(*   let mk_mapping op = *)
(*     let ll = List.filter_map (fun m -> StrMap.find_opt m op) ll in *)
(*     let ll = List.map IntMap.to_kv_list ll in *)
(*     match ll with *)
(*     | [] -> None *)
(*     | _ -> *)
(*         let ll = *)
(*           List.map (fun l -> *)
(*               let states = List.map fst l in *)
(*               let prop = smart_and @@ List.map snd l in *)
(*               (prop, states)) *)
(*           @@ List.choose_list_list ll *)
(*         in *)
(*         Some ll *)
(*   in *)
(*   CharMap.filter_map *)
(*     (fun se dest -> *)
(*       let op, _, phi = _get_sevent_fields [%here] se in *)
(*       let* l = mk_mapping op in *)
(*       let l = *)
(*         List.filter_map *)
(*           (fun (p, ns) -> *)
(*             if check_sat sim_ctx (smart_add_to p phi) then Some ns else None) *)
(*           l *)
(*       in *)
(*       match l with *)
(*       | [] -> None *)
(*       | [ ns ] -> Some ns *)
(*       | _ -> _die_with [%here] "multiple choices") *)
(*     m *)

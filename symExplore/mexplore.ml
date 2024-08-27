open Common
open Zzdatatype.Datatype
open Language
open SFA
open PathTree

type pstate = int state
type ptree = (int, C.t) path_tree
type ppath = (int, C.t) path
(* let terminate_filter (dfa : dfa list) (p : path) = *)
(*   let end_points = MPath.end_point p in *)
(*   List.combine dfa end_points *)
(*   |> List.for_all (fun (dfa, en) -> StateSet.mem en dfa.finals) *)

(* let request_length_filter (ctx : sym_explore_ctx) = *)
(*   MPath.to_ch_op_list *)
(*   #> (List.filter *)
(*         (StrMap.find "die" ctx.event_kindctx) #> ( function *)
(*         | Req -> true *)
(*         | _ -> false )) *)
(*   #> List.length *)
(*   #> (fun n -> n <= ctx.request_bound) *)

(* let path_length_filter n p = MPath.length p <= n *)

(* NOTE:
   dfa should be complete;
   although we have filter function; we still set a maximal bound to avoid finite loop
*)

let _default_path_lengt_bound = 200

type sym_explore_ctx = (Nt.t prop * SFA.dfa) list client
type rule = { incr : string; decr : string; resource : int }

let update_resource_ctx name =
  List.map (fun rule ->
      if String.equal rule.incr name then
        { rule with resource = rule.resource + 1 }
      else if String.equal rule.decr name then
        { rule with resource = rule.resource - 1 }
      else rule)

let is_valid_resource_ctx = List.for_all (fun rule -> rule.resource >= 0)

let init_resource_ctx =
  List.map (fun (incr, decr) -> { incr; decr; resource = 0 })

let expand_dfa_with_bound (dfa : dfa) rules bound =
  let counter = ref 0 in
  let next_node () =
    let res = !counter in
    counter := res + 1;
    res
  in
  let finals = ref StateSet.empty in
  (* let resource_ctx_map = Hashtbl.create 1000 in *)
  let new_next = ref StateMap.empty in
  let alter_next = dfa_next_to_ss_next dfa in
  (* return a new node when this node is valid *)
  (* let () = *)
  (*   Printf.printf "%i is mem of dfa?: %b\n" 6 (StateMap.mem 6 dfa.next) *)
  (* in *)
  let get_may_empty m name =
    match StateMap.find_opt name m with None -> StateMap.empty | Some s -> s
  in
  let rec aux (feul : int) resource_ctx actual_n =
    (* let () = *)
    (*   Printf.printf "[feul %i]visit %i(%i)\n" feul n (Hashtbl.find node_map n) *)
    (* in *)
    if feul <= 0 then
      if StateSet.mem actual_n dfa.finals then (
        let node = next_node () in
        finals := StateSet.add node !finals;
        Some node)
      else None
    else
      let m =
        Seq.filter_map
          (fun (dest, chs) ->
            (* let () = *)
            (*   Printf.printf "visit %i --> %i\n" (Hashtbl.find node_map n) dest *)
            (* in *)
            let chmap =
              CharSet.fold
                (fun ch ->
                  StrMap.update
                    (_get_sevent_name [%here] ch)
                    (function
                      | None -> Some (CharSet.singleton ch)
                      | Some chs -> Some (CharSet.add ch chs)))
                chs StrMap.empty
            in
            let chmap =
              StrMap.filter_map
                (fun op_name chs ->
                  let resource_ctx = update_resource_ctx op_name resource_ctx in
                  if is_valid_resource_ctx resource_ctx then
                    if feul <= 1 && not (StateSet.mem dest dfa.finals) then None
                    else
                      match aux (feul - 1) resource_ctx dest with
                      | None -> None
                      | Some node -> Some (node, chs)
                  else None)
                chmap
            in
            let m =
              StateMap.of_seq @@ List.to_seq @@ StrMap.to_value_list chmap
            in
            if StateMap.cardinal m == 0 then None else Some m)
          (StateMap.to_seq @@ get_may_empty alter_next actual_n)
      in
      let m =
        Seq.fold_left (StateMap.union (fun _ _ x -> Some x)) StateMap.empty m
      in
      if StateMap.cardinal m == 0 then None
      else
        let node = next_node () in
        let () =
          if StateSet.mem actual_n dfa.finals then
            finals := StateSet.add node !finals
        in
        (* Printf.printf "add %i -> [%s]\n" node *)
        (*   (List.split_by_comma string_of_int *)
        (*   @@ List.of_seq @@ Seq.map fst @@ StateMap.to_seq m); *)
        new_next := StateMap.add node m !new_next;
        Some node
  in
  let start = aux bound (init_resource_ctx rules) 0 in
  match start with
  | None -> None
  | Some start ->
      (* let finals = *)
      (*   List.filter (fun n -> StateSet.mem (Hashtbl.find node_map n) dfa.finals) *)
      (*   @@ List.init !counter (fun i -> i) *)
      (* in *)
      let res = { start; finals = !finals; next = ss_next_to_next !new_next } in
      let res' = SFA.minimize res in
      let () =
        Printf.printf "shrink states: %i -> %i\n" (num_states_dfa res)
          (num_states_dfa res')
      in
      let () =
        Printf.printf "shrink transitions: %i -> %i\n" (num_transition_dfa res)
          (num_transition_dfa res')
      in
      Some res'

let test__dfa_with_bound client =
  let rules =
    List.map (fun x -> (x.x, x.ty)) @@ ctx_to_list client.spec_tyctx.reqresp_ctx
  in
  (* let rules = *)
  (*   [ *)
  (*     ("eStartTxnReq", "eStartTxnRsp"); *)
  (*     ("eReadReq", "eReadRsp"); *)
  (*     ("eUpdateReq", "eUpdateRsp"); *)
  (*     ("eClientReq", "eClientResp"); *)
  (*     ("eClientReq", "eKVTime"); *)
  (*   ] *)
  (* in *)
  let violation =
    List.filter_map
      (fun (prop, dfa) ->
        let* dfa = expand_dfa_with_bound dfa rules client.step_bound in
        let dfa = SFA.normalize_dfa dfa in
        Some (prop, dfa))
      client.violation
  in
  { client with violation }

let bfs_with_filter (dfa : dfa) (filter : ptree -> ptree) =
  let rec bfs (fuel : int) (res : ptree) =
    let res = filter res in
    if fuel <= 0 then res
    else
      let res =
        append
          (fun en ->
            if not en.is_open then []
            else
              CharMap.fold
                (fun ch s res ->
                  (ch, mk_state s (StateSet.mem s dfa.finals) true) :: res)
                dfa.next #-> en.s [])
          res
      in
      bfs (fuel - 1) res
  in
  bfs _default_path_lengt_bound
    (PathLeaf (mk_state dfa.start (StateSet.mem dfa.start dfa.finals) true))

let check_sat (ctx : sym_explore_ctx) body =
  let rec aux world =
    match world with
    | WState -> body
    | WMap { qv; world; _ } -> Forall { qv; body = aux world }
    | WSingle { qv; world; _ } -> Exists { qv; body = aux world }
  in
  let query = aux ctx.violation_world in
  let res = sat_solver query in
  (* let () = Printf.printf "query[%b]: %s\n" res (layout_prop query) in *)
  (* let () = failwith "die" in *)
  res

let merge_ch ch1 (p2, ch2) =
  let op1, vs, phi1 = _get_sevent_fields [%here] ch1 in
  let op2, _, phi2 = _get_sevent_fields [%here] ch2 in
  if String.equal op1 op2 then
    let phi = smart_add_to (smart_implies p2 phi2) phi1 in
    if sat_solver phi then Some (EffEvent { op = op1; vs; phi }) else None
  else None

let merge_ptree (ppath1 : ptree) (ppath2 : ptree) =
  let rec aux = function
    | PathLeaf s1, PathLeaf s2 when s1.is_terminal && s2.is_terminal ->
        Some (PathLeaf s1)
    | PathLeaf _, PathLeaf _ ->
        (* let () = Printf.printf "??\n" in *)
        (* let () = failwith "die" in *)
        None
    | ( PathNode { parent; children },
        PathNode { parent = parent'; children = children' } ) ->
        let parent =
          {
            parent with
            is_terminal = parent.is_terminal && parent'.is_terminal;
          }
        in
        let children =
          List.map
            (fun (ch, tr) ->
              List.filter_map
                (fun (ch', tr') ->
                  let* ch = merge_ch ch (mk_true, ch') in
                  let* tr = aux (tr, tr') in
                  Some (ch, tr))
                children')
            children
          |> List.concat
        in
        Some (PathNode { parent; children })
    | _, _ -> _die [%here]
  in
  aux (ppath1, ppath2)

let bfs_with_filter_and_ptree (prop, dfa) (ptree : ptree) =
  let rec aux = function
    | PathLeaf s1, state ->
        if StateSet.mem state dfa.finals then Some (PathLeaf s1) else None
    | PathNode { parent; children }, state ->
        let parent =
          {
            parent with
            is_terminal = parent.is_terminal && StateSet.mem state dfa.finals;
          }
        in
        let next = dfa.next #-> state in
        let children =
          List.map
            (fun (ch, tr) ->
              CharMap.fold
                (fun ch' state' res ->
                  match
                    let* ch = merge_ch ch (prop, ch') in
                    let* tr = aux (tr, state') in
                    Some (ch, tr)
                  with
                  | None -> res
                  | Some x -> x :: res)
                next [])
            children
          |> List.concat
        in
        Some (PathNode { parent; children })
  in
  aux (ptree, dfa.start)

let ch_add_world (w_prop : Nt.t prop) ch =
  let op, vs, phi = _get_sevent_fields [%here] ch in
  EffEvent { op; vs; phi = smart_implies w_prop phi }

let ptree_add_world (w_prop : Nt.t prop) (ptree : ptree) =
  let rec aux = function
    | PathLeaf _ as s -> s
    | PathNode { parent; children } ->
        let children =
          List.map (fun (ch, tr) -> (ch_add_world w_prop ch, aux tr)) children
        in
        PathNode { parent; children }
  in
  aux ptree

let merge_ptrees ptrees =
  match ptrees with
  | [] -> None
  | ptree :: ptrees ->
      List.fold_left
        (fun res pt ->
          match res with None -> None | Some res -> merge_ptree res pt)
        (Some ptree) ptrees

(* let mbfs_with_filter (dfa : dfa list) (filter : MOpPath.path -> bool) *)
(*     (res_filter : MOpPath.path -> bool) = *)
(*   let open MOpPath in *)
(*   let rec bfs (fuel : int) (res : path list) (paths : path list) = *)
(*     (\* let () = Printf.printf "paths:\n%s\n" @@ Path.layout_paths_op paths in *\) *)
(*     let paths = List.filter (filter &&& fun p -> length p <= fuel) paths in *)
(*     match paths with *)
(*     | [] -> res *)
(*     | _ -> *)
(*         let res = res @ List.filter res_filter paths in *)
(*         if fuel <= 0 then res *)
(*         else *)
(*           let en = MOpPath.end_point cur in *)
(*           let nexts = *)
(*             List.map (fun (dfa, en) -> dfa.next #-> en) @@ List.combine dfa en *)
(*           in *)
(*           let tab = Hashtbl.create in *)
(*           let rec aux res nexts = *)
(*             match (res, nexts) with *)
(*             | None, [] -> _die [%here] *)
(*             | None, next :: nexts -> *)
(*                 CharMap.fold *)
(*                   (fun se dest p res -> *)
(*                     match p with *)
(*                     | Some p -> Some p *)
(*                     | None -> *)
(*                         let op, _, _ = *)
(*                           _get_sevent_fields [%here] se *)
(*                         in *)
(*                         res (aux (Some (op, [ dest ])) nexts)) *)
(*                   next None *)
(*             | Some (op, dests), [] -> *)
(*                   [MPath.(append cur (op, dests))] *)
(*             | Some (op, vs, phis, dests), next :: nexts -> *)
(*                 CharMap.fold *)
(*                   (fun se dest p -> *)
(*                     match p with *)
(*                     | Some p -> Some p *)
(*                     | None -> *)
(*                         let op', _, phi = *)
(*                           _get_sevent_fields [%here] se *)
(*                         in *)
(*                         if String.equal op' op then *)
(*                           aux *)
(*                             (Some (op, vs, phis @ [ phi ], dests @ [ dest ])) *)
(*                             nexts *)
(*                         else None) *)
(*                   next None *)
(*           in *)
(*           aux None nexts bfs (fuel - 1) res paths *)
(*   in *)
(*   bfs _default_path_lengt_bound [] [ PathEmpty dfa.start ] *)

let explore_counterexample_paths (ctx : sym_explore_ctx) (prop, dfa) =
  let ptree = bfs_with_filter dfa (prune_by_length ctx.step_bound) in
  (* let () = *)
  (*   Printf.printf "world: %s sizeof(tree) = %i\n" (layout_prop prop) *)
  (*     (num_pnode ptree) *)
  (* in *)
  let ptree' = prune_non_terminal ptree in
  (* let () = Printf.printf "sizeof(tree) = %i\n" (num_pnode ptree') in *)
  ptree_add_world prop ptree'

let mexplore_counterexample_paths (ctx : sym_explore_ctx) =
  List.map (explore_counterexample_paths ctx)

let pathtree_to_automata ptree =
  let ptree = rename_states ptree in
  let finals = StateSet.of_list @@ get_terminals ptree in
  let transitions = get_transitions ptree in
  let next =
    List.fold_right
      (fun (s, ch, d) -> dfa_next_insert s.s ch d.s)
      transitions StateMap.empty
  in
  { start = (get_root ptree).s; next; finals }

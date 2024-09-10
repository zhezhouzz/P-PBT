open Common
open Zzdatatype.Datatype
open Language
open SFA
open Path

type path = Path.path

let terminate_filter (dfa : dfa) (p : path) =
  StateSet.mem (Path.end_point p) dfa.finals

let last_non_request_filter (ctx : sym_explore_ctx) (p : path) =
  match p with
  | PathEmpty _ -> true
  | PathCons { ch; _ } -> (
      match
        StrMap.find "die" ctx.event_kindctx
          (_get_sevent_name __FILE__ __LINE__ ch)
      with
      | Req -> false
      | Resp | Hidden -> true)

let request_length_filter (ctx : sym_explore_ctx) =
  Path.to_ch_op_list
  #> (List.filter
        (StrMap.find "die" ctx.event_kindctx) #> ( function
        | Req -> true
        | _ -> false ))
  #> List.length
  #> (fun n -> n <= ctx.request_bound)

let path_length_filter n p = Path.length p <= n

(* NOTE:
   dfa should be complete;
   although we have filter function; we still set a maximal bound to avoid finite loop
*)

let _default_path_lengt_bound = 200

let bfs_with_filter (dfa : dfa) (filter : path -> bool)
    (res_filter : path -> bool) =
  let rec bfs (fuel : int) (res : path list) (paths : path list) =
    (* let () = Printf.printf "paths:\n%s\n" @@ Path.layout_paths_op paths in *)
    let paths = List.filter (filter &&& path_length_filter fuel) paths in
    match paths with
    | [] -> res
    | _ ->
        let res = res @ List.filter res_filter paths in
        if fuel <= 0 then res
        else
          let paths =
            List.map
              (fun prefix ->
                let en = Path.end_point prefix in
                CharMap.fold
                  (fun ch dest res -> Path.append prefix (ch, dest) :: res)
                  dfa.next #-> en [])
              paths
            |> List.concat
          in
          bfs (fuel - 1) res paths
  in
  bfs _default_path_lengt_bound [] [ PathEmpty dfa.start ]

let explore_counterexample_paths (ctx : sym_explore_ctx) (_, dfa) =
  bfs_with_filter dfa
    (request_length_filter ctx &&& path_length_filter ctx.step_bound)
    (terminate_filter dfa)

let simplify_via_paths paths (world_prop, dfa) =
  let rec bfs (state : state) (paths : path list) (trans, finals) =
    match paths with
    | [] -> (trans, finals)
    | _ ->
        let non_terminate_paths =
          List.filter_map Path.front_destruct_opt paths
        in
        let finals =
          if List.length non_terminate_paths < List.length paths then
            StateSet.add state finals
          else finals
        in
        CharMap.fold
          (fun ch dest (trans, finals) ->
            let sub_paths =
              List.filter_map
                (fun ((_, ch', _), p') ->
                  if 0 == C.compare ch ch' then Some p' else None)
                non_terminate_paths
            in
            let trans =
              if List.length sub_paths > 0 then
                dfa_next_insert state ch dest trans
              else trans
            in
            bfs dest sub_paths (trans, finals))
          dfa.next #-> state (trans, finals)
  in
  let next, finals = bfs dfa.start paths (StateMap.empty, StateSet.empty) in
  (world_prop, { start = dfa.start; finals; next })

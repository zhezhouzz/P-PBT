open Sugar
open Prop
open Zdatatype
open Common

let blist_to_prop (bl : bool list) int2lit =
  let blT, blF =
    map2 (List.map fst)
    @@ List.partition snd
    @@ List.mapi (fun i b -> (i, b)) bl
  in
  let blT, blF =
    map2
      (List.map (fun i -> lit_to_prop @@ IntMap.find "never" int2lit i))
      (blT, blF)
  in
  let blF = List.map (fun p -> Not p) blF in
  smart_and (blT @ blF)

let safe_check_sat_bool prop =
  let () = _assert [%here] "never" @@ List.is_empty (fv_prop prop) in
  let res = Prover.check_sat_bool prop in
  (* let () = Pp.printf "@{<bold>check sat(%b): @} %s\n" res (layout_prop prop) in *)
  res

let check_sat_fact { global_vars; desym_map; event_tyctx; _ }
    { global_fact; local_fact } =
  let global_prop = blist_to_prop global_fact desym_map.global_int2lit in
  let () =
    _assert [%here] "never"
    @@ Prover.check_sat_bool (smart_exists global_vars global_prop)
  in
  let do_local_fact op bl_set =
    let local_vars = StrMap.find "never" event_tyctx op in
    let int2lit = StrMap.find "never" desym_map.local_int2lit op in
    let check_sat local_prop =
      let prop =
        smart_forall global_vars @@ smart_exists local_vars
        @@ smart_implies global_prop local_prop
      in
      safe_check_sat_bool prop
    in
    BlistSet.filter (fun bl -> check_sat @@ blist_to_prop bl int2lit) bl_set
  in
  let local_fact = StrMap.mapi do_local_fact local_fact in
  { global_fact; local_fact }

let init_fact_tree checker ftab =
  let len = List.length ftab in
  let rec aux bl =
    if len == List.length bl then [ bl ]
    else
      let blT = bl @ [ true ] in
      let blF = bl @ [ false ] in
      (if checker blT then aux blT else [])
      @ if checker blF then aux blF else []
  in
  let res = aux [] in
  let layout_ratio a b =
    spf "%i/%i = %f" a b (float_of_int a /. float_of_int b)
  in
  let () =
    Pp.printf "@{<bold>Stat init_fact_tree@}: %s\n"
      (layout_ratio (List.length res) (pow 2 (List.length ftab)))
  in
  (* let () = if List.length res == 0 then _die [%here] in *)
  res

let init_fact_v2 prop
    { global_ftab; local_ftab; desym_map; event_tyctx; global_vars; _ } =
  let do_local_fact op ftab =
    let local_vars = StrMap.find "never" event_tyctx op in
    let int2lit = StrMap.find "never" desym_map.local_int2lit op in
    let checker bl =
      (* let prop = *)
      (*   smart_forall global_vars @@ smart_exists local_vars *)
      (*   @@ smart_implies prop (blist_to_prop bl int2lit) *)
      (* in *)
      let prop =
        smart_exists global_vars @@ smart_exists local_vars
        @@ smart_add_to prop (blist_to_prop bl int2lit)
      in
      safe_check_sat_bool prop
    in
    let fvecs = init_fact_tree checker ftab in
    BlistSet.of_list fvecs
  in
  let checker bl =
    let p = blist_to_prop bl desym_map.global_int2lit in
    Prover.check_valid (smart_forall global_vars (smart_implies prop p))
  in
  let global_fact = init_fact_tree checker global_ftab in
  match global_fact with
  | [] -> None
  | [ global_fact ] ->
      let local_fact = StrMap.mapi do_local_fact local_ftab in
      Some { global_fact; local_fact }
  | _ ->
      let () =
        List.iter
          (fun bl ->
            Pp.printf "%s\n" @@ layout_prop
            @@ blist_to_prop bl desym_map.global_int2lit)
          global_fact
      in
      _die_with [%here]
        "the global prop contains multipel global feature vectors"

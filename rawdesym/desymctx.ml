open Myconfig
open Sugar
open Prop
open Zdatatype
open Fa
open Common
open SFA
open Desymeval

let mk_fvec_from_ftab ftab =
  let len = List.length ftab in
  let l = List.init (pow 2 len) (fun i -> IntBinary.int_to_bin (len, i)) in
  BlistSet.of_list l

let init_fact prop { global_ftab; local_ftab; desym_map; _ } =
  let global_fact = mk_fvec_from_ftab global_ftab in
  let global_fact =
    BlistSet.filter
      (fun bl ->
        let m = align_map (desym_map.global_lit2int, Array.of_list bl) in
        desym_eval_prop m prop)
      global_fact
  in
  let global_fact =
    BlistSet.filter
      (fun bl ->
        let p = Satcheck.blist_to_prop bl desym_map.global_int2lit in
        Prover.check_sat_bool p)
      global_fact
  in
  let global_fact =
    if BlistSet.cardinal global_fact == 1 then BlistSet.choose global_fact
    else
      let () =
        BlistSet.iter
          (fun bl ->
            Pp.printf "%s\n" @@ layout_prop
            @@ Satcheck.blist_to_prop bl desym_map.global_int2lit)
          global_fact
      in
      _die_with [%here]
        "the global prop contains multipel global feature vectors"
  in
  let local_fact = StrMap.map mk_fvec_from_ftab local_ftab in
  { global_fact; local_fact }

let mk_li_map =
  List.fold_lefti
    (fun (lit2int, int2lit) i lit ->
      (LitMap.add lit i lit2int, IntMap.add i lit int2lit))
    (LitMap.empty, IntMap.empty)

let mk_desym_map (global_ftab, local_ftab) =
  let global_lit2int, global_int2lit = mk_li_map global_ftab in
  let local_lit2int = StrMap.map (fun l -> fst @@ mk_li_map l) local_ftab in
  let local_int2lit = StrMap.map (fun l -> snd @@ mk_li_map l) local_ftab in
  { global_lit2int; global_int2lit; local_lit2int; local_int2lit }

let get_in_regex (get_in_chars, union, empty) =
  let rec aux r =
    match r with
    | Empty | Eps -> empty
    | MultiChar cs -> get_in_chars cs
    | Alt (r1, r2) | Inters (r1, r2) -> union (aux r1) (aux r2)
    | Seq rs -> List.fold_right (fun r -> union (aux r)) rs empty
    | Comple (cs, r) ->
        let fv1 = get_in_chars cs in
        let fv2 = aux r in
        union fv1 fv2
    | Star r -> aux r
  in
  aux

let get_global_vars_in_char { vs; phi; _ } =
  let vs = TVSet.of_list vs in
  let fvs = fv_prop phi in
  let fvs = List.filter (fun x -> not (TVSet.mem x vs)) fvs in
  TVSet.of_list fvs

let get_global_vars_in_chars cs =
  CharSet.fold (fun c -> TVSet.union (get_global_vars_in_char c)) cs TVSet.empty

let get_global_vars_in_reg =
  get_in_regex (get_global_vars_in_chars, TVSet.union, TVSet.empty)

let get_constant_in_char { phi; _ } = ConstSet.of_list @@ get_consts phi

let get_constant_in_chars cs =
  CharSet.fold
    (fun c -> ConstSet.union (get_constant_in_char c))
    cs ConstSet.empty

let get_constant_in_reg =
  get_in_regex (get_constant_in_chars, ConstSet.union, ConstSet.empty)

let get_constant_in_char { phi; _ } = LitSet.of_list @@ get_lits phi

let get_lits_in_chars cs =
  CharSet.fold (fun c -> LitSet.union (get_constant_in_char c)) cs LitSet.empty

let get_lits_in_reg r =
  LitSet.map norm_order_lit
  @@ get_in_regex (get_lits_in_chars, LitSet.union, LitSet.empty) r

let mybuild_euf vars =
  let vars = List.map (fun lit -> lit #: (lit_to_nt lit)) vars in
  let space = Hashtbl.create 10 in
  let () =
    List.iter
      (fun { x; ty } ->
        match Hashtbl.find_opt space ty with
        | None -> Hashtbl.add space ty [ x ]
        | Some l -> Hashtbl.replace space ty (x :: l))
      vars
  in
  let aux ty vars =
    let pairs = List.cross vars vars in
    let pairs =
      List.filter (function x, y -> compare_lit Nt.compare_nt x y > 0) pairs
    in
    (* let () = *)
    (*   Pp.printf "@{<bold>pairs:@} %s\n" *)
    (*     (List.split_by_comma *)
    (*        (function x, y -> spf "(%s, %s)" (layout_lit x) (layout_lit y)) *)
    (*        pairs) *)
    (* in *)
    let eqlits =
      List.map (fun l -> match l with x, y -> mk_lit_eq_lit ty x y) pairs
    in
    eqlits
  in
  let res =
    Hashtbl.fold
      (fun ty vars res ->
        if
          List.length vars > 1 && not (Nt.equal_nt ty (Nt.Ty_uninter "Bytes.t"))
        then aux ty vars @ res
        else res)
      space []
  in
  (* let () = *)
  (*   Pp.printf "@{<bold>mybuild_euf:@} %s\n" (List.split_by_comma layout_lit res) *)
  (* in *)
  res

let mk_ftab if_add_lt (vars : (Nt.nt, string) typed list) (cs : constant list) =
  (* Remove boolean constants *)
  let bvars, vars =
    List.partition (fun x -> Nt.equal_nt x.ty Nt.Ty_bool) vars
  in
  let cs = List.filter (function B _ -> false | _ -> true) cs in
  let lits = List.map (fun x -> AVar x) vars @ List.map (fun x -> AC x) cs in
  let () =
    _log "desym" @@ fun _ ->
    Pp.printf "@{<bold>lits:@} %s\n" (List.split_by_comma layout_lit lits)
  in
  let additional =
    if if_add_lt then
      let int_lits =
        List.filter (fun lit -> Nt.equal_nt Nt.Ty_int @@ lit_to_nt lit) lits
      in
      let () =
        _log "desym" @@ fun _ ->
        Pp.printf "@{<bold>int lits:@} %s\n"
          (List.split_by_comma layout_lit int_lits)
      in
      let pairs = List.combination_l int_lits 2 in
      let ltlits =
        let lt = ">" #: Nt.(construct_arr_tp ([ Ty_int; Ty_int ], Ty_bool)) in
        List.map
          (fun l ->
            match l with
            | [ x; y ] -> AAppOp (lt, [ x #: Nt.Ty_int; y #: Nt.Ty_int ])
            | _ -> _die [%here])
          pairs
      in
      let () =
        _log "desym" @@ fun _ ->
        Pp.printf "@{<bold>ltlits:@} %s\n"
          (List.split_by_comma layout_lit ltlits)
      in
      ltlits
    else []
  in
  let res = List.map (fun x -> AVar x) bvars @ mybuild_euf lits @ additional in
  res

let mk_global_const (prop, r) =
  List.of_seq @@ ConstSet.to_seq
  @@ ConstSet.union (get_constant_in_reg r) (ConstSet.of_list (get_consts prop))

let refine_global_ftab global_vars prop ftab =
  let check_valid_feature lit =
    let aux lit =
      let p = smart_forall global_vars (smart_implies prop lit) in
      let res = Prover.check_valid p in
      let () =
        _log "desym" @@ fun _ ->
        Pp.printf "@{<bold> check valid: @} %s :: %b\n" (layout_prop p) res
      in
      res
    in
    let res =
      (not (aux (lit_to_prop lit))) && not (aux @@ Not (lit_to_prop lit))
    in
    let () =
      _log "desym" @@ fun _ ->
      Pp.printf "@{<bold>res: @} %s :: %b\n" (layout_lit lit) res
    in
    res
  in
  List.filter check_valid_feature ftab

let layout_ftab ftab =
  spf "[%i] %s\n" (List.length ftab) (List.split_by_comma layout_lit ftab)

(* let mk_global_ftab _ (global_vars, prop, r) = *)
(*   let () = Pp.printf "start mk_global_ftab \n" in *)
(*   (\* let if_add_lt = *\) *)
(*   (\*   match Typectx.get_opt tyctx ">" with None -> false | Some _ -> true *\) *)
(*   (\* in *\) *)
(*   let constants = mk_global_const (prop, r) in *)
(*   let global_ftab = mk_ftab false global_vars constants in *)
(*   let () = Pp.printf "@{<bold>global_ftab:@} %s\n" (layout_ftab global_ftab) in *)
(*   let ftab = get_lits prop in *)
(*   let ftab = *)
(*     List.filter *)
(*       (fun lit -> *)
(*         List.for_all (fun x -> *)
(*             List.exists (fun y -> String.equal y.x x) global_vars) *)
(*         @@ fv_lit_id lit) *)
(*       ftab *)
(*   in *)
(*   let global_ftab = *)
(*     List.slow_rm_dup (fun x y -> compare_lit Nt.compare_nt x y == 0) *)
(*     @@ List.map norm_order_lit @@ global_ftab @ ftab *)
(*   in *)
(*   (\* let () = Pp.printf "@{<bold>ftab:@} %s\n" (layout_ftab global_ftab) in *\) *)
(*   (\* let global_ftab = refine_global_ftab global_vars prop global_ftab in *\) *)
(*   let () = Pp.printf "@{<bold>ftab:@} %s\n" (layout_ftab global_ftab) in *)
(*   let () = Pp.printf "end mk_global_ftab \n" in *)
(*   global_ftab *)

let mk_global_ftab _ (_, prop, r) =
  let { global_lits; _ } = gather_regex @@ raw_regex_to_regex r in
  let prop_lits = get_lits prop in
  (* let if_add_lt = *)
  (*   match Typectx.get_opt tyctx ">" with None -> false | Some _ -> true *)
  (* in *)
  let global_ftab =
    List.slow_rm_dup (fun x y -> compare_lit Nt.compare_nt x y == 0)
    @@ List.map norm_order_lit @@ global_lits @ prop_lits
  in
  (* let () = Pp.printf "@{<bold>ftab:@} %s\n" (layout_ftab global_ftab) in *)
  (* let global_ftab = refine_global_ftab global_vars prop global_ftab in *)
  let () =
    _log "desym" @@ fun _ ->
    Pp.printf "@{<bold>global_ftab:@} %s\n" (layout_ftab global_ftab)
  in
  global_ftab

let mk_desym_ctx tyctx event_tyctx (gprop, r) =
  let event_tyctx = Typectx.ctx_to_map event_tyctx in
  let gvars = TVSet.of_list @@ fv_prop gprop in
  let global_vars =
    List.of_seq @@ TVSet.to_seq (TVSet.union gvars @@ get_global_vars_in_reg r)
  in
  (* let if_add_lt = *)
  (*   match Typectx.get_opt tyctx ">" with None -> false | Some _ -> true *)
  (* in *)
  (* let constants = mk_global_const (gprop, r) in *)
  let global_ftab = mk_global_ftab tyctx (global_vars, gprop, r) in
  let local_ftab =
    StrMap.map
      (fun local_vars ->
        (* let ftab = mk_ftab if_add_lt (global_vars @ local_vars) constants in *)
        let ftab = List.of_seq @@ LitSet.to_seq @@ get_lits_in_reg r in
        (* let ftab = *)
        (*   List.of_seq @@ LitSet.to_seq *)
        (*   @@ LitSet.union (get_lits_in_reg r) (LitSet.of_list ftab) *)
        (* in *)
        let local_vars_id = List.map _get_x local_vars in
        let ftab =
          List.filter
            (fun lit ->
              not
                (List.is_empty
                @@ List.interset String.equal local_vars_id (fv_lit_id lit)))
            ftab
        in
        ftab)
      event_tyctx
  in
  let desym_map = mk_desym_map (global_ftab, local_ftab) in
  let res = { global_vars; event_tyctx; global_ftab; local_ftab; desym_map } in
  let () = _log "desym" @@ fun _ -> print_desym_ctx res in
  res

(* type desym_fact = { *)
(*   global_fact : bool *)
(*   event_tyctx : (Nt.nt, string) typed list Typectx.ctx; *)
(*   event_ftab : LitSet.t StrMap.t; *)
(* } *)

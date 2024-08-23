open Language
open Zzdatatype.Datatype
open Register
open Pprop
module S2D = SFA.CharMap
module D2S = DesymFA.CharMap

let final_states_decl =
  "final_states" #: (mk_p_map_ty Nt.Ty_int (mk_p_set_ty Nt.Ty_int))

let final_states_init_function_decl = "final_states_init" #: Nt.Ty_unit
let transition_init_function_name = "transition_init_function"
let transition_init_function_decl = transition_init_function_name #: Nt.Ty_unit
let transition_name = "transitions"

type pfa = {
  name : string;
  spec_tyctx : spec_tyctx;
  global_prop_map : Nt.t prop IntMap.t;
  actions : ((Nt.t, string) typed list * Nt.t prop list) StrMap.t;
  action_qvs_map : (Nt.t, string) typed list StrMap.t;
  mapping : int IntMap.t StrMap.t StateMap.t IntMap.t;
  finals : StateSet.t IntMap.t;
  d2s : Nt.t sevent D2S.t;
  s2d : (string * int) S2D.t;
  (* the p part *)
  p_finals : (Nt.t, string) typed;
  p_final_init_function : (Nt.t, string) typed;
  p_transitions : (Nt.t, string) typed;
  p_transitions_init_function : (Nt.t, string) typed;
  p_prop_func : (Nt.t, string) typed * int -> (Nt.t, string) typed;
  p_gprop_func : int -> (Nt.t, string) typed;
}

let compute_qvs_from_prop_id pfa (op, i) =
  let _, vs, phi = _get_sevent_fields [%here] @@ D2S.find (op, i) pfa.d2s in
  let fv = compute_qvs_from_prop (vs, phi) in
  fv

(** Finals *)

let mk_p_finals name =
  (spf "%s_%s" name final_states_decl.x) #: final_states_decl.ty

let mk_p_final_init_function name =
  (spf "%s_%s" name final_states_init_function_decl.x)
  #: final_states_init_function_decl.ty

let mk_final_states_init_function_decl pfa =
  let m =
    IntMap.map
      (fun ss final_states_expr ->
        let ss = List.of_seq @@ StateSet.to_seq ss in
        let e =
          mk_p_assign (final_states_expr, mk_p_default final_states_expr.ty)
        in
        let es =
          List.map (fun s -> mk_p_add_set final_states_expr (mk_p_int s)) ss
        in
        mk_p_seqs_ (e :: es))
      pfa.finals
  in
  let body = init_p_int_map m (mk_pid pfa.p_finals) in
  (pfa.p_final_init_function, mk_p_function_decl [] [] body)

(** Transitions *)

let transtion_type =
  mk_p_map_ty Nt.Ty_int (* the global prop index *) raw_transition_type

let mk_p_transitions name = (spf "%s_%s" name transition_name) #: transtion_type

let mk_p_transitions_init_function name =
  (spf "%s_%s" name transition_init_function_decl.x)
  #: transition_init_function_decl.ty

let mk_transition_init_function pfa =
  let mapping =
    IntMap.map
      (StateMap.map
         (StrMap.map (IntMap.map (fun i e -> mk_p_assign (e, mk_p_int i)))))
      pfa.mapping
  in
  let mapping = IntMap.map (StateMap.map (StrMap.map init_p_int_map)) mapping in
  let mapping = IntMap.map (StateMap.map init_p_str_map) mapping in
  let mapping = IntMap.map init_p_int64_map mapping in
  let body = init_p_int_map mapping (mk_pid pfa.p_transitions) in
  (pfa.p_transitions_init_function, mk_p_function_decl [] [] body)

let register_pfa pfa m =
  let m = machine_register_local_vars [ pfa.p_finals; pfa.p_transitions ] m in
  let pprops =
    D2S.fold
      (fun (op, i) se l ->
        let _, vs, phi = _get_sevent_fields [%here] se in
        (op, i, vs, phi) :: l)
      pfa.d2s []
  in
  let gpprops, pprops =
    List.partition
      (fun (op, _, _, _) -> String.equal op global_event_name)
      pprops
  in
  let pprop_decls = List.filter_map (mk_prop_func_decl pfa.name) pprops in
  let gpprop_decls = List.map (mk_gprop_func_decl pfa.name) gpprops in
  let m =
    machine_register_local_funcs
      ([
         mk_final_states_init_function_decl pfa; mk_transition_init_function pfa;
       ]
      @ pprop_decls @ gpprop_decls)
      m
  in
  m

let concretlize_atuoamta name spec_tyctx reg =
  let open SFA in
  let globals, regs =
    List.split @@ List.mapi (fun i (global, reg) -> ((i, global), (i, reg))) reg
  in
  let global_prop_map = IntMap.of_seq @@ List.to_seq globals in
  (* let () = *)
  (*   Printf.printf "globals\n%s\n" *)
  (*     (List.split_by "\n" *)
  (*        (fun (i, prop) -> spf "%i:%s;" i (layout_prop prop)) *)
  (*        globals) *)
  (* in *)
  let finals =
    IntMap.of_seq @@ List.to_seq
    @@ List.map (fun (i, dfa) -> (i, dfa.finals)) regs
  in
  let mapping = List.map (fun (i, reg) -> (i, reg.next)) regs in
  let get_actions mapping =
    let ses =
      List.of_seq @@ Seq.concat
      @@ Seq.map (fun m -> Seq.map fst @@ CharMap.to_seq m)
      @@ Seq.map snd @@ StateMap.to_seq mapping
    in
    let m =
      List.fold_left
        (fun m se ->
          match se with
          | GuardEvent _ -> _die [%here]
          | EffEvent { op; vs; phi } ->
              StrMap.update op
                (function
                  | None -> Some (vs, [ phi ])
                  | Some (vs, phis) -> Some (vs, phi :: phis))
                m)
        StrMap.empty ses
    in
    m
  in
  let ms =
    List.fold_left
      (fun m (_, mapping) ->
        let m' = get_actions mapping in
        StrMap.union (fun _ (_, l1) (vs, l2) -> Some (vs, l1 @ l2)) m m')
      StrMap.empty mapping
  in
  let m =
    StrMap.map
      (fun (vs, l) ->
        (vs, List.slow_rm_dup (fun a b -> 0 == Stdlib.compare a b) l))
      ms
  in
  let actions = m in
  let action_qvs_map =
    StrMap.map
      (fun (vs, props) -> compute_qvs_from_prop (vs, And props))
      actions
  in
  (* NOTE: also had global ones *)
  let m = StrMap.add global_event_name ([], List.map snd globals) m in
  (* let event_typing_ctx = StrMap.map (fun (vs, _) -> mk_p_record_ty vs) m in *)
  let s2d, d2s =
    StrMap.fold
      (fun op (vs, props) (s2d, d2s) ->
        let s2d =
          List.fold_lefti
            (fun s2d i phi -> S2D.add (EffEvent { op; vs; phi }) (op, i) s2d)
            s2d props
        in
        let d2s =
          List.fold_lefti
            (fun d2s i phi -> D2S.add (op, i) (EffEvent { op; vs; phi }) d2s)
            d2s props
        in
        (s2d, d2s))
      m (S2D.empty, D2S.empty)
  in
  (* let () = *)
  (*   Printf.printf "s2d\n%s\n" *)
  (*     (List.split_by_comma layout_se *)
  (*        (List.of_seq @@ Seq.map fst @@ S2D.to_seq s2d)) *)
  (* in *)
  let mk_mapping mapping =
    let mapping =
      StateMap.map
        (fun m ->
          D2S.of_seq
          @@ Seq.map (fun (c, s) ->
                 (* let () = Printf.printf "%s\n" (layout_se c) in *)
                 (CharMap.find c s2d, s))
          @@ CharMap.to_seq m)
        mapping
    in
    let mk_precise (m : state D2S.t) =
      let l = List.of_seq @@ D2S.to_seq m in
      let m =
        List.fold_right
          (fun ((op, i), state) ->
            StrMap.update op (function
              | None -> Some (IntMap.singleton i state)
              | Some m' -> Some (IntMap.add i state m')))
          l StrMap.empty
      in
      m
    in
    StateMap.map mk_precise mapping
  in
  let mapping =
    IntMap.of_seq @@ List.to_seq
    @@ List.map
         (fun (i, mapping) ->
           let _, global_prop =
             List.find "die" (fun (i', _) -> i == i') globals
           in
           let global_event =
             EffEvent { op = global_event_name; vs = []; phi = global_prop }
           in
           let _, id = S2D.find global_event s2d in
           (id, mk_mapping mapping))
         mapping
  in
  let p_prop_func (op, id) = prop_func_decl name (op, id) in
  let p_gprop_func id = global_prop_func_decl name id in
  {
    name;
    global_prop_map;
    spec_tyctx;
    actions;
    action_qvs_map;
    mapping;
    finals;
    d2s;
    s2d;
    p_finals = mk_p_finals name;
    p_final_init_function = mk_p_final_init_function name;
    p_transitions = mk_p_transitions name;
    p_transitions_init_function = mk_p_transitions_init_function name;
    p_prop_func;
    p_gprop_func;
  }

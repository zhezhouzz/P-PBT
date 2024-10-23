open Language
open Zdatatype
open Common

module SampleDomain = Map.Make (struct
  type t = Nt.t

  let compare = Nt.compare_nt
end)

type runtime = {
  sample_domain : constant list SampleDomain.t;
  trace : trace;
  buffer : trace;
  store : constant StrMap.t;
  event_rtyctx : SFA.raw_regex haft ctx;
}

exception RuntimeInconsistent of runtime

let layout_store store =
  List.split_by " ;" (fun (x, c) -> spf "%s --> %s" x (layout_constant c))
  @@ StrMap.to_kv_list store

let layout_runtime { trace; buffer; store; _ } =
  spf "{ history: %s\n  buffer: %s\n  store: %s}\n" (layout_trace trace)
    (layout_trace buffer) (layout_store store)

let default_sample_domain =
  SampleDomain.of_seq @@ List.to_seq
  @@ [
       (Nt.Ty_int, List.map (fun n -> I n) [ -1; 0; 1; 2 ]);
       (Nt.Ty_bool, List.map (fun n -> B n) [ true; false ]);
       (mk_p_abstract_ty "rid", List.map (fun n -> I n) [ 1; 2; 3 ]);
       (mk_p_abstract_ty "aid", List.map (fun n -> I n) [ 4; 5; 6 ]);
       (mk_p_abstract_ty "tGid", List.map (fun n -> I n) [ 1; 2; 3 ]);
       (mk_p_abstract_ty "tKey", List.map (fun n -> I n) [ 4; 5; 6 ]);
       (mk_p_abstract_ty "tVal", List.map (fun n -> I n) [ 7; 8; 9 ]);
     ]

let init_runtime (env : syn_env) sample_domain =
  {
    sample_domain;
    trace = [];
    buffer = [];
    store = StrMap.empty;
    event_rtyctx = env.event_rtyctx;
  }

let store_add (vs, cs) store =
  StrMap.add_seq
    (List.to_seq
    @@ List.map (fun (x, c) -> (x.x, c))
    @@ _safe_combine [%here] vs cs)
    store

let reduce_cty c ({ phi; _ } : cty) =
  eval_prop (StrMap.singleton default_v c) phi

let reduce_sevent (op', cs) = function
  | { op; vs; phi } ->
      String.equal op op' && eval_prop (store_add (vs, cs) StrMap.empty) phi

let sample runtime qv =
  match qv.ty with
  | Nt.Ty_enum { enum_elems; enum_name } ->
      let elem = choose_from_list enum_elems in
      let c = Enum { enum_elems; enum_name; elem } in
      (qv.x, c)
  | _ -> (
      match SampleDomain.find_opt qv.ty runtime.sample_domain with
      | None ->
          let () =
            Printf.printf "cannot find sample domain of type (%s)\n"
              (Nt.layout qv.ty)
          in
          _die [%here]
      | Some cs -> (qv.x, choose_from_list cs))

let reduce_haft runtime cs (tau : SFA.raw_regex haft) =
  let rec aux (tau, cs) =
    (* let () = *)
    (*   Pp.printf "@{<bold>reduce_haft:@} cs(%s)\n%s\n" *)
    (*     (List.split_by_comma layout_constant cs) *)
    (*     (layout_haft SFA.layout_raw_regex tau) *)
    (* in *)
    match (tau, cs) with
    | RtyHAParallel { history; parallel; _ }, [] ->
        if SFA.is_match reduce_sevent history runtime.trace then [ parallel ]
        else []
    | RtyGArr { arg; argnt; retrty }, cs ->
        let samples = SampleDomain.find argnt runtime.sample_domain in
        let ress =
          List.concat_map
            (fun c ->
              let retrty = subst_haft arg (AC c) retrty in
              aux (retrty, cs))
            samples
        in
        ress
    | RtyArr { arg; argcty; retrty }, c :: cs ->
        if reduce_cty c argcty then
          let retrty = subst_haft arg (AC c) retrty in
          aux (retrty, cs)
        else []
    | RtyInter (tau1, tau2), _ -> aux (tau1, cs) @ aux (tau2, cs)
    | _, _ -> _die [%here]
  in
  match aux (tau, cs) with [] -> _die [%here] | l -> choose_from_list l

let sample_phi runtime (vs, prop) =
  let rec aux (n : int) =
    if n <= 0 then
      let () =
        Printf.printf "vs: %s; prop: %s\n" (layout_qvs vs) (layout_prop prop)
      in
      _die_with [%here] "sample too many times"
    else
      let store = List.map (sample runtime) vs in
      let store' = StrMap.add_seq (List.to_seq store) runtime.store in
      if eval_prop store' prop then store (* List.map snd store *)
      else aux (n - 1)
  in
  aux 1000

let mk_assume runtime (vs, prop) =
  let store = sample_phi runtime (vs, prop) in
  let store' = StrMap.add_seq (List.to_seq store) runtime.store in
  { runtime with store = store' }

let sample_event runtime = function
  | { op; vs; phi } ->
      let store = sample_phi runtime (vs, phi) in
      let cs = List.map snd store in
      (op, cs)

let send runtime (op, cs) =
  let tau = _get_force [%here] runtime.event_rtyctx op in
  let ses = reduce_haft runtime cs tau in
  let msgs = List.map (sample_event runtime) ses in
  {
    runtime with
    trace = runtime.trace @ [ (op, cs) ];
    buffer = runtime.buffer @ msgs;
  }

let recv_and_send runtime op =
  let rec aux = function
    | [] ->
        let () =
          Pp.printf
            "@{<red>@{<bold>runtime error:@}@} cannot recv message(%s)\n" op
        in
        raise (RuntimeInconsistent runtime)
    | ((op', args) as elem) :: buffer ->
        if String.equal op op' then (args, buffer)
        else
          let args, buffer = aux buffer in
          (args, elem :: buffer)
  in
  let args, buffer = aux runtime.buffer in
  let runtime = send { runtime with buffer } (op, args) in
  (runtime, args)

let gen runtime elem = { runtime with buffer = runtime.buffer @ [ elem ] }

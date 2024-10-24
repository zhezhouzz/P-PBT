open Language
open Common
open Runtime

let counter = ref 0

let rec eval (runtime, term) =
  let () = counter := !counter + 1 in
  let () =
    _log "eval" @@ fun _ ->
    let () = Pp.printf "@{<bold>Eval(%i):@}\n" !counter in
    let () = Pp.printf "@{<blue>Runtime:@}\n%s\n" (layout_runtime runtime) in
    let () = Pp.printf "@{<orange>Term:@}\n%s\n" (layout_term term) in
    ()
  in
  match term with
  | CVal v ->
      let c = eval_value runtime.store v.x in
      (runtime, [ c ])
  | CLetE { lhs; rhs = { x = CAssume (_, prop); _ }; body } ->
      let runtime = Runtime.mk_assume runtime (lhs, prop) in
      eval (runtime, body.x)
  | CLetE { lhs; rhs = { x = CObs { op; prop }; _ }; body } ->
      let runtime, cs = recv_and_send runtime op.x in
      let store = store_add (lhs, cs) runtime.store in
      let runtime = { runtime with store } in
      if eval_prop runtime.store prop then eval (runtime, body.x)
      else raise (RuntimeInconsistent runtime)
  | CLetE { lhs; rhs; body } ->
      (* let runtime, cs = *)
      (*   List.fold_right *)
      (*     (fun e (runtime, cs) -> *)
      (*       let runtime, c =  eval (runtime, e) in *)
      (*       (runtime, c :: cs)) *)
      (*     rhs (runtime, []) *)
      (* in *)
      let runtime, cs = eval (runtime, rhs.x) in
      let store = store_add (lhs, cs) runtime.store in
      eval ({ runtime with store }, body.x)
  | CAppOp { op; args } ->
      (runtime, [ eval_app_op op (meval_value runtime.store args) ])
  | CObs _ ->
      _die_with [%here] "never"
      (* let runtime, cs = recv_and_send runtime op.x in *)
      (* if eval_prop runtime.store prop then (runtime, cs) *)
      (* else raise (RuntimeInconsistent runtime) *)
  | CGen { op; args } ->
      let args = meval_value runtime.store args in
      let runtime = send runtime (op.x, args) in
      (runtime, [])
  | CUnion [] -> _die_with [%here] "never"
  | CUnion es -> eval (runtime, choose_from_list es)
  | CAssert v ->
      if const_to_bool [%here] @@ eval_value runtime.store v then (runtime, [])
      else raise (RuntimeInconsistent runtime)
  | CAssertP phi ->
      if eval_prop runtime.store phi then (runtime, [])
      else raise (RuntimeInconsistent runtime)
  | CAssume _ -> _die_with [%here] "never"

and eval_single_return (runtime, term) =
  let runtime, res = eval (runtime, term) in
  match res with [ v ] -> (runtime, v) | _ -> _die [%here]

let eval_until_consistent (runtime, term) =
  let rec aux (i : int) =
    let () = counter := 0 in
    if i > 1000 then _die_with [%here] "too many time until consistent"
    else
      try (i, eval (runtime, term)) with
      | RuntimeInconsistent _ -> aux (i + 1)
      | e -> raise e
  in
  let i, res = aux 0 in
  let () = Pp.printf "@{<red>Repeat for %i times@}\n" i in
  res

let eval_sample (runtime, term) total =
  let rec aux (successed : int) (used : int) =
    if used >= total then successed
    else
      try
        let _ = eval (runtime, term) in
        aux (successed + 1) (used + 1)
      with
      | RuntimeInconsistent _ -> aux successed (used + 1)
      | e -> raise e
  in
  aux 0 0

open Language
open AutomataLibrary

let init_env =
  {
    goal = None;
    event_tyctx = emp;
    gen_ctx = emp;
    tyctx = emp;
    event_rtyctx = emp;
  }

let add_to_env env = function
  | PrimDecl { name; nt } ->
      { env with tyctx = add_to_right env.tyctx name #: nt }
  | MsgNtDecl { generative; name; nt } ->
      let l =
        match nt with
        | Nt.Ty_record l -> l
        | Nt.Ty_unit -> []
        | _ -> _die [%here]
      in
      let event_tyctx = add_to_right env.event_tyctx name #: l in
      let gen_ctx = add_to_right env.gen_ctx name #: generative in
      { env with event_tyctx; gen_ctx }
  | MsgDecl _ -> env
  | SynGoal _ -> env

(* let mk_input_env env items = *)
(*   let rec aux (event_tyctx, gen_ctx, tyctx, goal) = function *)
(*     | PrimDecl { name; nt } -> *)
(*         (event_tyctx, gen_ctx, add_to_right tyctx name #: nt, goal) *)
(*     | MsgNtDecl { generative; name; nt } -> *)
(*         let l = match nt with Nt.Ty_record l -> l | _ -> _die [%here] in *)
(*         let event_tyctx = add_to_right event_tyctx name #: l in *)
(*         let gen_ctx = add_to_right gen_ctx name #: generative in *)
(*         (event_tyctx, gen_ctx, tyctx, goal) *)
(*     | MsgDecl _ -> (event_tyctx, gen_ctx, tyctx, goal) *)
(*     | SynGoal goal -> *)
(*         let _ = *)
(*           match goal with *)
(*           | Some _ -> _die_with [%here] "multiple goals" *)
(*           | _ -> () *)
(*         in *)
(*         (event_tyctx, gen_ctx, tyctx, Some goal) *)
(*   in *)
(*   let event_tyctx, gen_ctx, tyctx, goal = *)
(*     List.fold_left aux (emp, emp, emp, None) items *)
(*   in *)
(*   let goal = *)
(*     match goal with None -> _die_with [%here] "no goals" | Some goal -> goal *)
(*   in *)
(*   { goal; event_tyctx; gen_ctx; tyctx; event_rtyctx = emp } *)

let handle_reg env reg =
  let op_names = List.map _get_x (ctx_to_list env.event_tyctx) in
  let reg =
    desugar env.event_tyctx (SyntaxSugar (CtxOp { op_names; body = reg }))
  in
  let reg = delimit_context delimit_cotexnt_se reg in
  SFA.regex_to_raw reg

let map_fa_haft f haft =
  let rec aux t =
    match t with
    | RtyBase cty -> RtyBase cty
    | RtyHAF { history; adding; future } ->
        let history, adding, future = map3 f (history, adding, future) in
        RtyHAF { history; adding; future }
    | RtyHAParallel { history; adding_se; parallel } ->
        let history = f history in
        RtyHAParallel { history; adding_se; parallel }
    | RtyArr { arg; argcty; retrty } ->
        RtyArr { arg; argcty; retrty = aux retrty }
    | RtyInter (t1, t2) -> RtyInter (aux t1, aux t2)
  in
  aux haft

let handle_haft env haft = map_fa_haft (handle_reg env) haft

(* NOTE: the whole spec items are first-order *)
let item_check env = function
  | MsgDecl { name; haft } ->
      let haft =
        Normal_rty_typing.bi_haft_check env.event_tyctx env.tyctx haft
      in
      {
        env with
        event_rtyctx =
          add_to_right env.event_rtyctx name #: (handle_haft env haft);
      }
  | SynGoal { qvs; prop } -> (
      match env.goal with
      | Some _ -> _die_with [%here] "multiple goals"
      | _ ->
          let tyctx = add_to_rights env.tyctx qvs in
          let regex_ctx = mk_regex_ctx (env.event_tyctx, tyctx) in
          let prop = _get_x @@ bi_symbolic_regex_check regex_ctx prop in
          { env with goal = Some { qvs; prop } })
  | _ -> env

let struct_check env l =
  let env = List.fold_left add_to_env env l in
  let () = Printf.printf "%s\n" (layout_syn_env env) in
  let l = List.map (locally_rename_item env.event_tyctx) l in
  let env = List.fold_left item_check env l in
  env

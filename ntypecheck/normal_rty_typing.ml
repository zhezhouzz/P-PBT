open Language
open AutomataLibrary

let bi_cty_check ctx { nt; phi } =
  let ctx = add_to_right ctx default_v #: nt in
  let phi = Typecheck.bi_typed_prop_check ctx phi in
  { nt; phi }

let rec bi_haft_check event_tyctx tyctx = function
  | RtyBase cty -> RtyBase (bi_cty_check tyctx cty)
  | RtyHAF { history; adding; future } ->
      let regex_ctx = mk_regex_ctx (event_tyctx, tyctx) in
      let history, adding, future =
        map3
          (fun x -> _get_x @@ bi_symbolic_regex_check regex_ctx x)
          (history, adding, future)
      in
      RtyHAF { history; adding; future }
  | RtyHAParallel { history; adding_se; parallel } ->
      let regex_ctx = mk_regex_ctx (event_tyctx, tyctx) in
      let () =
        _log "ntypecheck" @@ fun _ ->
        Pp.printf "@{<bold>ctx@}: %s" (layout_ctx Nt.layout regex_ctx.tyctx);
        Pp.printf "@{<bold>check HAF@}: %s\n\n"
          (layout_haft layout_symbolic_regex
             (RtyHAParallel { history; adding_se; parallel }))
      in
      let history = _get_x @@ bi_symbolic_regex_check regex_ctx history in
      let adding_se = bi_sevent_check regex_ctx adding_se in
      let parallel =
        List.map
          (fun se ->
            let () =
              _log "ntypecheck" @@ fun _ ->
              Pp.printf "@{<bold>ctx@}: %s"
                (layout_ctx Nt.layout regex_ctx.tyctx);
              Pp.printf "@{<bold>se@}: %s\n\n" (layout_se se)
            in
            bi_sevent_check regex_ctx se)
          parallel
      in
      RtyHAParallel { history; adding_se; parallel }
  | RtyArr { arg; argcty; retrty } ->
      let argcty = bi_cty_check tyctx argcty in
      let tyctx = add_to_right tyctx arg #: (erase_cty argcty) in
      let retrty = bi_haft_check event_tyctx tyctx retrty in
      RtyArr { arg; argcty; retrty }
  | RtyGArr { arg; argnt; retrty } ->
      let tyctx = add_to_right tyctx arg #: argnt in
      let retrty = bi_haft_check event_tyctx tyctx retrty in
      RtyGArr { arg; argnt; retrty }
  | RtyInter (t1, t2) ->
      RtyInter
        (bi_haft_check event_tyctx tyctx t1, bi_haft_check event_tyctx tyctx t2)

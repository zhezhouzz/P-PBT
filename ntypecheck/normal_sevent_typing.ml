open Normal_prop_typing
open Language

(* type t = Nt.t *)

let bi_sevent_check (ctx : spec_tyctx) (sevent : Nt.t sevent) : Nt.t sevent =
  match sevent with
  | GuardEvent { vs; phi } ->
      let bindings = (List.map (Nt.__force_typed [%here])) vs in
      let ctx' = add_to_rights ctx.tyctx bindings in
      let phi = bi_typed_prop_check ctx' phi in
      let res = GuardEvent { vs = bindings; phi } in
      res
  | EffEvent { op; vs; phi } -> (
      match get_opt ctx.event_tyctx op with
      | None -> _failatwith [%here] (spf "undefined event: %s" op)
      | Some argsty ->
          let vs =
            match vs with
            | [] -> List.map (fun { x; ty } -> (x, { x; ty })) argsty
            | _ ->
                List.map
                  (fun ({ x; ty }, { x = y; ty = ty' }) ->
                    (* let () = *)
                    (*   Printf.printf "%s: %s ?= %s\n" op (layout ty) (Nt.layout ty') *)
                    (* in *)
                    (x, { x = y; ty = Nt.__type_unify [%here] ty ty' }))
                  (_safe_combine [%here] vs argsty)
          in
          let phi =
            List.fold_right
              (fun (x, y) -> subst_prop_instance x (AVar y))
              vs phi
          in
          let _, vs = List.split vs in
          (* we always add the server type *)
          (* let vs = (__server_feild #: (Some server_type)) :: vs in *)
          let bindings = List.map (Nt.__force_typed [%here]) vs in
          let ctx' = add_to_rights ctx.tyctx bindings in
          let phi = bi_typed_prop_check ctx' phi in
          let res = EffEvent { op; vs = bindings; phi } in
          (* let () = Printf.printf "SE: %s\n" @@ layout_se res in *)
          res)

let bi_label_check = bi_sevent_check

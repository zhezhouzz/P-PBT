open Normal_prop_typing
open Language

(* type t = Nt.t *)

let bi_sevent_check (ctx : spec_tyctx) (sevent : Nt.t option sevent) :
    Nt.t sevent =
  match sevent with
  | GuardEvent _ -> _die [%here]
  (* | GuardEvent { vs; phi } -> *)
  (*     let bindings = *)
  (*       default_serv_field :: (List.map (__force_typed __FILE__ __LINE__)) vs *)
  (*     in *)
  (*     let ctx' = add_to_rights ctx.tyctx bindings in *)
  (*     let phi = bi_typed_prop_check ctx' phi in *)
  (*     let res = GuardEvent { vs = bindings; phi } in *)
  (*     res *)
  | EffEvent { op; vs; phi } -> (
      match get_opt ctx.event_tyctx op with
      | None -> _failatwith __FILE__ __LINE__ (spf "undefined event: %s" op)
      | Some argsty ->
          let vs =
            match vs with
            | [] -> List.map (fun (x, ty) -> (x, { x; ty = Some ty })) argsty
            | _ ->
                List.map
                  (fun ({ x; ty }, (y, ty')) ->
                    (* let () = *)
                    (*   Printf.printf "%s: %s ?= %s\n" op (layout ty) (Nt.layout ty') *)
                    (* in *)
                    let ty =
                      Ntopt.__type_unify Ntopt.layout __FILE__ __LINE__ ty
                        (Some ty')
                    in
                    (x, { x = y; ty }))
                  (_safe_combine __FILE__ __LINE__ vs argsty)
          in
          let phi =
            List.fold_right
              (fun (x, y) -> subst_prop_instance x (AVar y))
              vs phi
          in
          let _, vs = List.split vs in
          (* we always add the server type *)
          (* let vs = (__server_feild #: (Some server_type)) :: vs in *)
          let bindings = List.map (__force_typed __FILE__ __LINE__) vs in
          let ctx' = add_to_rights ctx.tyctx bindings in
          let phi = bi_typed_prop_check ctx' phi in
          let res = EffEvent { op; vs = bindings; phi } in
          (* let () = Printf.printf "SE: %s\n" @@ layout_se res in *)
          res)

let bi_label_check = bi_sevent_check

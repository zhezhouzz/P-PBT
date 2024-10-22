open Language
open Zdatatype
open Common
open Gamma

let quantifier_elimination (qvs, gprop, qv, local_qvs, prop) =
  let () = Printf.printf "remove qv: %s\n" (layout_qv qv) in
  let () = Printf.printf "qvs: %s\n" (layout_qvs qvs) in
  let () = Printf.printf "prop: %s\n" (layout_prop prop) in
  (* let check_valid_feature lit = *)
  (*   let aux prop = *)
  (*     Prover.check_valid (smart_forall (qv :: qvs) @@ smart_implies gprop prop) *)
  (*   in *)
  (*   (not (aux @@ lit_to_prop lit)) && not (aux @@ Not (lit_to_prop lit)) *)
  (* in *)
  (* let check_valid_pre prop = *)
  (*   not *)
  (*     (Prover.check_valid *)
  (*        (smart_forall (qv :: qvs) @@ smart_implies gprop (Not prop))) *)
  (* in *)
  let check_valid abd =
    let p =
      smart_forall (qv :: qvs)
      @@ smart_exists local_qvs @@ smart_exists qvs
      @@ smart_implies (smart_add_to abd gprop) prop
    in
    let () = Printf.printf "check: %s\n" @@ layout_prop p in
    Prover.check_valid p
  in
  if check_valid mk_true then Some mk_true
  else
    let cs = get_consts prop in
    let lits =
      List.map (fun x -> (AVar x) #: x.ty) qvs
      @ List.map (fun c -> (AC c) #: (constant_to_nt c)) cs
    in
    let lits = List.filter (fun lit -> Nt.equal_nt qv.ty lit.ty) lits in
    let fvtab =
      List.map (fun lit -> mk_lit_eq_lit qv.ty (AVar qv) lit.x) lits
    in
    let () =
      Printf.printf "fvtab: %s\n" @@ List.split_by_comma layout_lit @@ fvtab
    in
    let fvs = List.init (List.length fvtab) (fun _ -> [ true; false ]) in
    let fvs = List.choose_list_list fvs in
    let fvs =
      List.map
        smart_and
        #. (List.mapi (fun idx x ->
                let lit = lit_to_prop @@ List.nth fvtab idx in
                if x then lit else Not lit))
        fvs
    in
    let fvs = List.filter check_valid fvs in
    (* let () = Printf.printf "res: %s\n" @@ layout_prop (smart_or fvs) in *)
    match fvs with [] -> None | _ -> Some (smart_or fvs)

let rec to_top_cnf phi =
  match phi with And ps -> List.concat_map to_top_cnf ps | _ -> [ phi ]

let instantiation_var env (gamma : Gamma.gamma) vs Gamma.{ bvs; bprop } =
  let cs = get_consts bprop in
  let lits = List.map tv_to_lit (gamma.bvs @ vs) @ List.map c_to_lit cs in
  let fvtab = Abduction.build_fvtab env lits in
  let fvtab =
    List.filter
      (fun lit ->
        let s =
          List.interset String.equal (List.map _get_x vs) (fv_lit_id lit)
        in
        not (List.is_empty s))
      fvtab
  in
  (* let check_valid_feature lit = *)
  (*   let aux prop = *)
  (*     Prover.check_valid *)
  (*       (smart_forall gamma.bvs @@ smart_implies gamma.bprop prop) *)
  (*   in *)
  (*   (not (aux @@ lit_to_prop lit)) && not (aux @@ Not (lit_to_prop lit)) *)
  (* in *)
  let check_valid_pre prop =
    not
      (Prover.check_valid
         (smart_forall gamma.bvs @@ smart_implies gamma.bprop (Not prop)))
  in
  let check_valid abd =
    let p =
      smart_forall (gamma.bvs @ vs)
      @@ smart_exists bvs
      @@ smart_implies (smart_add_to abd gamma.bprop) bprop
    in
    let () = Printf.printf "check: %s\n" @@ layout_prop p in
    Prover.check_valid p
  in
  let fvs = List.init (List.length fvtab) (fun _ -> [ true; false ]) in
  let fvs = List.choose_list_list fvs in
  let fvs =
    List.map
      smart_and
      #. (List.mapi (fun idx x ->
              let lit = lit_to_prop @@ List.nth fvtab idx in
              if x then lit else Not lit))
      fvs
  in
  let fvs = List.filter check_valid_pre fvs in
  let fvs = List.filter check_valid fvs in
  let () = Printf.printf "res: %s\n" @@ layout_prop (smart_or fvs) in
  match fvs with
  | [] -> _die [%here]
  | _ ->
      let zprop' = smart_or fvs in
      let gamma =
        Gamma.{ bvs = gamma.bvs @ vs; bprop = smart_add_to zprop' gamma.bprop }
      in
      (gamma, zprop')

let instantiation env goal =
  let get_fvargs gamma args qvs =
    let args' = List.filter (Gamma.not_mem gamma) args in
    let qvs' = List.filter (tv_not_mem args) qvs in
    let () =
      Printf.printf
        "get_fvargs:::\n\
         gamma: %s $$$ vargs: %s $$$ qvs: %s\n\
         ==>args: %s $$$ qvs: %s\n"
        (layout_qvs gamma.bvs) (layout_qvs args) (layout_qvs qvs)
        (layout_qvs args') (layout_qvs qvs')
    in
    (args', qvs')
  in
  let rec handle gamma (gamma', plan) =
    let () =
      Printf.printf "Gamma: %s\n" (Gamma.layout gamma);
      layout_syn_plan_judgement goal
    in
    match plan with
    | [] -> if 0 == List.length gamma'.bvs then mk_term_tt else _die [%here]
    | PlanAct { op; args } :: plan ->
        let () =
          Pp.printf "@{<bold>Work on:@} %s\n"
            (Plan.layout_elem (PlanAct { op; args }))
        in
        let fargs, qvs = get_fvargs gamma args gamma'.bvs in
        let gamma' = { bvs = qvs; bprop = gamma'.bprop } in
        let gamma, prop' = instantiation_var env gamma fargs gamma' in
        let e = handle gamma (gamma', plan) in
        if is_gen env op then
          (* let e = *)
          (*   mk_term_assertP prop' *)
          (*   @@ mk_term_gen env op (List.map (fun x -> VVar x) args) e *)
          (* in *)
          mk_term_assume fargs prop'
          @@ mk_term_gen env op (List.map (fun x -> VVar x) args) e
        else
          let args' =
            List.map
              (fun x ->
                if name_in_qvs x.x fargs then x
                else (Rename.unique "tmp") #: x.ty)
              args
          in
          let ps =
            List.filter_map (fun (x, y) ->
                if String.equal x.x y.x then None
                else
                  let lit = mk_lit_eq_lit x.ty (AVar x) (AVar y) in
                  Some (lit_to_prop lit))
            @@ _safe_combine [%here] args' args
          in
          let p = smart_and (ps @ [ prop' ]) in
          (* let e = mk_term_obs env op args' (mk_term_assertP p e) in *)
          let e = mk_term_obs env op args' p e in
          e
    | _ :: _ -> _die [%here]
  in
  let prog = handle Gamma.emp goal in
  let () = Pp.printf "@{<bold>Prog@}:\n%s\n" (layout_term prog) in
  prog

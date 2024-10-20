open Language

type gamma = { bvs : (Nt.nt, string) typed list; bprop : Nt.nt prop }

let mem { bvs; _ } = tv_mem bvs
let not_mem { bvs; _ } = tv_not_mem bvs
let emp = { bvs = []; bprop = mk_true }
let layout { bvs; bprop } = spf "{%s | %s}" (layout_qvs bvs) (layout_prop bprop)

let check_valid { bvs; bprop } prop =
  let q = smart_forall bvs @@ smart_implies bprop prop in
  let res = Prover.check_valid q in
  (* let () = *)
  (*   Pp.printf "@{<bold> check valid: @} %s :: %b\n" (layout_prop q) res *)
  (* in *)
  res

let check_sat { bvs; bprop } prop =
  let q = smart_forall bvs @@ smart_implies bprop prop in
  let res = Prover.check_sat_bool q in
  (* let () = Pp.printf "@{<bold> check sat: @} %s :: %b\n" (layout_prop q) res in *)
  res

let smart_not p =
  if is_true p then mk_false
  else if is_false p then mk_true
  else match p with Not p -> p | _ -> Not p

let peval_prop litsT litsF =
  let setT = Rawdesym.LitSet.of_list litsT in
  let setF = Rawdesym.LitSet.of_list litsF in
  let rec aux e =
    match e with
    | Lit lit ->
        if Rawdesym.LitSet.mem (Rawdesym.norm_order_lit lit.x) setT then mk_true
        else if Rawdesym.LitSet.mem (Rawdesym.norm_order_lit lit.x) setF then
          mk_false
        else Lit lit
    | Implies (e1, e2) -> smart_implies (aux e1) (aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not e -> smart_not (aux e)
    | And es -> smart_and (List.map aux es)
    | Or es -> smart_or (List.map aux es)
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Forall _ -> _die [%here]
    | Exists _ -> _die [%here]
  in
  aux

open Zdatatype

let simplify gamma =
  let lits = List.map Rawdesym.norm_order_lit @@ get_lits gamma.bprop in
  let lits = List.slow_rm_dup eq_lit lits in
  let litsT =
    List.filter
      (fun lit ->
        Prover.check_valid
          (smart_forall gamma.bvs (smart_implies gamma.bprop (lit_to_prop lit))))
      lits
  in
  let litsF =
    List.filter
      (fun lit ->
        Prover.check_valid
          (smart_forall gamma.bvs
             (smart_implies gamma.bprop (Not (lit_to_prop lit)))))
      lits
  in
  let () =
    Pp.printf "@{<bold>litsT:@} %s\n" (List.split_by_comma layout_lit litsT)
  in
  let () =
    Pp.printf "@{<bold>litsF:@} %s\n" (List.split_by_comma layout_lit litsF)
  in
  let bprop = peval_prop litsT litsF gamma.bprop in
  let pT = smart_and (List.map lit_to_prop litsT) in
  let pF = smart_and (List.map (fun lit -> Not (lit_to_prop lit)) litsF) in
  let bprop = smart_and [ bprop; pT; pF ] in
  let () =
    Pp.printf "@{<bold>Gamma.simplify:@} %s -->\n%s\n" (layout_prop gamma.bprop)
      (layout_prop bprop)
  in
  { gamma with bprop }

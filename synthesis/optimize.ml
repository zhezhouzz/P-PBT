open Language
open Common
open Gamma

let lit_to_equation = function
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x ->
      if is_var_c a.x && is_var_c b.x then Some (a.x, b.x) else None
  | _ -> None

let eq_in_prop_to_subst_map { bvs; bprop } =
  let conjs = to_conjs bprop in
  let lits = List.filter_map to_lit_opt conjs in
  let eqs = List.filter_map lit_to_equation lits in
  let eqvs =
    List.filter_map (function AVar x, AVar y -> Some (x, y) | _ -> None) eqs
  in
  let subst_eqs x lit = List.map (map2 (subst_name_qv x lit)) in
  let rec aux (eqs, res) =
    match eqs with
    | [] -> res
    | (x, y) :: eqs ->
        let comp a b =
          let c = compare (String.length a) (String.length b) in
          if c == 0 then compare a b else c
        in
        let c = comp x.x y.x in
        (* let () = Printf.printf "\tCompare %s %s = %i\n" x.x y.x c in *)
        if c == 0 then aux (eqs, res)
        else if c > 0 then
          let res = res @ [ (x.x, y) ] in
          let eqs = subst_eqs x.x y eqs in
          aux (eqs, res)
        else
          let res = res @ [ (y.x, x) ] in
          let eqs = subst_eqs y.x x eqs in
          aux (eqs, res)
  in
  let m = aux (eqvs, []) in
  let prop =
    List.fold_right (fun (x, lit) -> subst_prop_instance x (AVar lit)) m bprop
  in
  let bvs =
    List.filter
      (fun x -> not (List.exists (fun (y, _) -> String.equal x.x y) m))
      bvs
  in
  let bprop = simpl_eq_in_prop prop in
  ({ bvs; bprop }, m)

let optimize_back_goal ((gamma, (a, b, c)) as goal) args =
  let gamma = Gamma.simplify gamma in
  let gamma, m = eq_in_prop_to_subst_map gamma in
  let a, c = map2 (msubst Plan.subst_plan m) (a, c) in
  let b = msubst Plan.subst_elem m b in
  let goal' = (gamma, (a, b, c)) in
  let args' =
    List.filter
      (fun x -> not (List.exists (fun (y, _) -> String.equal x.x y) m))
      args
  in
  let () =
    Printf.printf "Optimize:\n (%s)\n" (layout_qvs args);
    layout_syn_back_judgement goal;
    Printf.printf "==>\n (%s) \n" (layout_qvs args');
    layout_syn_back_judgement goal'
  in
  (args', goal')

let optimize_goal ((gamma, reg) : plan sgoal) =
  let gamma, m = eq_in_prop_to_subst_map gamma in
  (gamma, msubst Plan.subst_plan m reg)

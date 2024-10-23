open Language
open Common
open Gamma
open AutomataLibrary

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
  let () = simp_print_opt_plan_judgement goal m goal' in
  (* let () = *)
  (*   Printf.printf "Optimize:\n (%s)\n" (layout_qvs args); *)
  (*   layout_syn_back_judgement goal; *)
  (*   Printf.printf "==>\n (%s) \n" (layout_qvs args'); *)
  (*   layout_syn_back_judgement goal' *)
  (* in *)
  (args', goal')

let optimize_back_goal_also_record ((gamma, (a, b, c)) as goal) args record =
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
    record :=
      match !record with
      | None -> None
      | Some elem -> Some (msubst Plan.subst_elem m elem)
  in
  let () = simp_print_opt_plan_judgement goal m goal' in
  (* let () = *)
  (*   Printf.printf "Optimize:\n (%s)\n" (layout_qvs args); *)
  (*   layout_syn_back_judgement goal; *)
  (*   Printf.printf "==>\n (%s) \n" (layout_qvs args'); *)
  (*   layout_syn_back_judgement goal' *)
  (* in *)
  (args', goal')

let optimize_goal ((gamma, reg) : plan sgoal) =
  let gamma, m = eq_in_prop_to_subst_map gamma in
  (gamma, msubst Plan.subst_plan m reg)

(** optimize prop *)

let to_fvec_lit = function
  | Lit lit -> Some (lit.x, true)
  | Not (Lit lit) -> Some (lit.x, false)
  | _ -> None

(* let* l = aux prop in *)
(* let l = List.sort (fun a b -> compare_lit Nt.compare_nt (fst a) (fst b)) l in *)
(* Some (List.split l) *)

let to_fvec_clauze prop =
  let rec aux = function
    | And l ->
        let l' = List.concat @@ List.filter_map aux l in
        if List.length l' == List.length l then Some l' else None
    | _ as p ->
        let* cell = to_fvec_lit p in
        Some [ cell ]
  in
  aux prop

let to_fvec_dnf =
  let rec aux = function
    | Or l ->
        let l' = List.concat @@ List.filter_map aux l in
        if List.length l' == List.length l then Some l' else None
    | _ as p ->
        let* cell = to_fvec_clauze p in
        Some [ cell ]
  in
  aux

(* let unify_dnf ftab ll = *)
(*   let try_true i ll = *)
(*     List.for_all (fun l -> List.nth l i) ll *)
(*   in *)
(*   let try_false i ll = *)
(*     List.for_all (fun l -> not (List.nth l i)) ll *)
(*   in *)
(*   let simp (ftab, ll) = *)
(*     let rec res (ftab, ll) = *)

(*   let rec aux ftab ll = *)
(*     match (ftab, ll) with *)
(*     | [], [] -> [[]] *)
(*     | lit :: ftab, _ -> *)
(*       let lt = List.filter_map (function true :: l-> Some l | _ -> None) ll in *)
(*       let lf = List.filter_map (function false :: l-> Some l | _ -> None) ll in *)
(*       let lt = aux ftab lt in *)
(*       let lf = aux ftab lt in *)

(*       [lit, true] *)

module Predictable = struct
  type lit = Nt.t Prop.lit
  type prop = Nt.t Prop.prop

  let mk_true = mk_true
  let mk_false = mk_false
  let mk_lit lit = Lit lit #: Nt.Ty_bool
  let mk_ite cond bencht benchf = Ite (Lit cond #: Nt.Ty_bool, bencht, benchf)
  let mk_and = smart_add_to
  let mk_or l1 l2 = smart_or [ l1; l2 ]
  let mk_not p = Not p
  let layout_lit = layout_lit
  let layout_prop = layout_prop
end

module DT = Dtree.Dt.F (Predictable)

let simp_fvec_prop_opt prop =
  let do_sort =
    List.sort (fun a b -> compare_lit Nt.compare_nt (fst a) (fst b))
  in
  let ftab =
    List.sort (fun a b -> compare_lit Nt.compare_nt a b) @@ get_lits prop
  in
  if List.length ftab == 0 then None
  else
    let* dnf = to_fvec_dnf prop in
    let dnf' =
      List.filter_map
        (fun l ->
          let ftab', l = List.split @@ do_sort l in
          if List.equal (equal_lit Nt.equal_nt) ftab ftab' then Some l else None)
        dnf
    in
    let* pos =
      if List.length dnf == List.length dnf' then Some dnf' else None
    in
    let prop = DT.classify_as_prop (Array.of_list ftab) pos in
    (* let len = List.length ftab in *)
    (* let total = List.init (pow 2 len) (fun x -> x) in *)
    (* let total = *)
    (*   List.map (fun n -> Rawdesym.IntBinary.int_to_bin (len, n)) total *)
    (* in *)
    (* let neg = *)
    (*   List.filter *)
    (*     (fun l -> not (List.exists (List.equal Bool.equal l) pos)) *)
    (*     total *)
    (* in *)
    Some prop

let simp_fvec_prop prop =
  match simp_fvec_prop_opt prop with Some prop -> prop | None -> prop

let simp_fvec_se { op; vs; phi } = { op; vs; phi = simp_fvec_prop phi }
let simp_fvec_cs cs = SFA.CharSet.map simp_fvec_se cs
let simp_fvec_raw_regex r = SFA.raw_reg_map simp_fvec_cs r

let simp_fvec_elem = function
  | PlanActBuffer { op; args; phi } ->
      PlanActBuffer { op; args; phi = simp_fvec_prop phi }
  | PlanAct { op; args } -> PlanAct { op; args }
  | PlanSe { op; vs; phi } -> PlanSe { op; vs; phi = simp_fvec_prop phi }
  | PlanStarInv cs -> PlanStarInv (simp_fvec_cs cs)
  | PlanStar r -> PlanStar (simp_fvec_raw_regex r)

let simp_fvec_plan = List.map simp_fvec_elem

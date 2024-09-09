open Ast
open Lit

let layout_sexp_prop regex =
  Sexplib.Sexp.to_string @@ sexp_of_prop (fun _ -> Sexplib.Sexp.unit) regex

let typed_eq = equal_typed (fun _ _ -> true)

let rec fv_prop (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> [] @ typed_fv_lit _t__tlittyped0
  | Implies (_tprop0, _tprop1) -> ([] @ fv_prop _tprop1) @ fv_prop _tprop0
  | Ite (_tprop0, _tprop1, _tprop2) ->
      (([] @ fv_prop _tprop2) @ fv_prop _tprop1) @ fv_prop _tprop0
  | Not _tprop0 -> [] @ fv_prop _tprop0
  | And _tproplist0 -> [] @ List.concat (List.map fv_prop _tproplist0)
  | Or _tproplist0 -> [] @ List.concat (List.map fv_prop _tproplist0)
  | Iff (_tprop0, _tprop1) -> ([] @ fv_prop _tprop1) @ fv_prop _tprop0
  | Forall { qv; body } ->
      Zdatatype.List.substract (typed_eq String.equal)
        ([] @ fv_prop body)
        [ qv ]
  | Exists { qv; body } ->
      Zdatatype.List.substract (typed_eq String.equal)
        ([] @ fv_prop body)
        [ qv ]

and typed_fv_prop (prop_e : ('t, 't prop) typed) = fv_prop prop_e.x

let rec subst_prop (string_x : string) f (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> Lit (typed_subst_lit string_x f _t__tlittyped0)
  | Implies (_tprop0, _tprop1) ->
      Implies (subst_prop string_x f _tprop0, subst_prop string_x f _tprop1)
  | Ite (_tprop0, _tprop1, _tprop2) ->
      Ite
        ( subst_prop string_x f _tprop0,
          subst_prop string_x f _tprop1,
          subst_prop string_x f _tprop2 )
  | Not _tprop0 -> Not (subst_prop string_x f _tprop0)
  | And _tproplist0 -> And (List.map (subst_prop string_x f) _tproplist0)
  | Or _tproplist0 -> Or (List.map (subst_prop string_x f) _tproplist0)
  | Iff (_tprop0, _tprop1) ->
      Iff (subst_prop string_x f _tprop0, subst_prop string_x f _tprop1)
  | Forall { qv; body } ->
      if String.equal qv.x string_x then Forall { qv; body }
      else Forall { qv; body = subst_prop string_x f body }
  | Exists { qv; body } ->
      if String.equal qv.x string_x then Exists { qv; body }
      else Exists { qv; body = subst_prop string_x f body }

and typed_subst_prop (string_x : string) f (prop_e : ('t, 't prop) typed) =
  (subst_prop string_x f) #-> prop_e

let rec map_prop (f : 't -> 's) (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> Lit (typed_map_lit f _t__tlittyped0)
  | Implies (_tprop0, _tprop1) ->
      Implies (map_prop f _tprop0, map_prop f _tprop1)
  | Ite (_tprop0, _tprop1, _tprop2) ->
      Ite (map_prop f _tprop0, map_prop f _tprop1, map_prop f _tprop2)
  | Not _tprop0 -> Not (map_prop f _tprop0)
  | And _tproplist0 -> And (List.map (map_prop f) _tproplist0)
  | Or _tproplist0 -> Or (List.map (map_prop f) _tproplist0)
  | Iff (_tprop0, _tprop1) -> Iff (map_prop f _tprop0, map_prop f _tprop1)
  | Forall { qv; body } -> Forall { qv = f #=> qv; body = map_prop f body }
  | Exists { qv; body } -> Exists { qv = f #=> qv; body = map_prop f body }

and typed_map_prop (f : 't -> 's) (prop_e : ('t, 't prop) typed) =
  (map_prop f) #-> (f #=> prop_e)

let fv_prop_id e = fv_typed_id_to_id fv_prop e
let typed_fv_prop_id e = fv_typed_id_to_id typed_fv_prop e

let subst_prop_instance x instance e =
  subst_f_to_instance subst_prop x instance e

let typed_subst_prop_instance x instance e =
  subst_f_to_instance typed_subst_prop x instance e
(* Generated from _prop.ml *)

(* force *)
let prop_force_typed_lit_opt prop =
  match prop with Lit lit -> Some lit | _ -> None

let get_cbool prop =
  match prop with Lit { x = AC (B b); _ } -> Some b | _ -> None

let mk_true = Lit (AC (B true)) #: Nt.Ty_bool
let mk_false = Lit (AC (B false)) #: Nt.Ty_bool
let is_true p = match get_cbool p with Some true -> true | _ -> false
let is_false p = match get_cbool p with Some false -> true | _ -> false

open Zdatatype

let unfold_and prop =
  let rec aux = function
    | [] -> []
    | And l :: l' -> aux (l @ l')
    | prop :: l' -> prop :: aux l'
  in
  let l = aux prop in
  List.slow_rm_dup pr l

let smart_and l =
  let l = unfold_and l in
  if List.exists is_false l then mk_false
  else
    match List.filter (fun p -> not (is_true p)) l with
    | [] -> mk_true
    | [ x ] -> x
    | l -> And l

let unfold_or prop =
  let rec aux = function
    | [] -> []
    | Or l :: l' -> aux (l @ l')
    | prop :: l' -> prop :: aux l'
  in
  let l = aux prop in
  List.slow_rm_dup eq_prop l

let smart_or l =
  let l = unfold_or l in
  if List.exists is_true l then mk_true
  else
    match List.filter (fun p -> not (is_false p)) l with
    | [] -> mk_false
    | [ x ] -> x
    | l -> Or l

let smart_add_to (a : 't prop) (prop : 't prop) =
  match get_cbool a with
  | Some true -> prop
  | Some false -> mk_false
  | None -> (
      match prop with
      | And props -> smart_and (a :: props)
      | _ -> smart_and [ a; prop ])

let smart_implies a prop =
  match get_cbool a with
  | Some true -> prop
  | Some false -> mk_true
  | None -> Implies (a, prop)

let get_lits prop =
  let rec aux e res =
    match e with
    | Lit { x = AC _; _ } -> res
    | Lit lit -> (
        let litopt = get_non_unit_lit lit in
        match litopt with None -> res | Some lit -> lit :: res)
    | Implies (e1, e2) -> aux e1 @@ aux e2 res
    | Ite (e1, e2, e3) -> aux e1 @@ aux e2 @@ aux e3 res
    | Not e -> aux e res
    | And es -> List.fold_right aux es res
    | Or es -> List.fold_right aux es res
    | Iff (e1, e2) -> aux e1 @@ aux e2 res
    | Forall _ -> _die [%here]
    | Exists _ -> _die [%here]
  in
  let (lits : Nt.t lit list) = aux prop [] in
  (* let () = *)
  (*   Printf.printf ">>>>> get_lits: %s\n" *)
  (*     (List.split_by_comma layout_sexp_lit lits) *)
  (* in *)
  Zdatatype.List.slow_rm_dup eq_lit lits

let build_euf vars =
  let space = Hashtbl.create 10 in
  let () =
    List.iter
      (fun { x; ty } ->
        match Hashtbl.find_opt space ty with
        | None -> Hashtbl.add space ty [ x ]
        | Some l -> Hashtbl.replace space ty (x :: l))
      vars
  in
  let aux ty vars =
    let pairs = List.combination_l vars 2 in
    let eqlits =
      List.map
        (fun l ->
          match l with [ x; y ] -> mk_lit_eq_lit ty x y | _ -> _die [%here])
        pairs
    in
    eqlits
  in
  let res =
    Hashtbl.fold
      (fun ty vars res ->
        if
          List.length vars > 1 && not (Nt.equal_nt ty (Nt.Ty_uninter "Bytes.t"))
        then aux ty vars @ res
        else res)
      space []
  in
  res

open Ast

let rec fv_lit (lit_e : 't lit) =
  match lit_e with
  | AC _ -> []
  | AVar _t_stringtyped0 -> [] @ [ _t_stringtyped0 ]
  | ATu _t__tlittypedlist0 ->
      [] @ List.concat (List.map typed_fv_lit _t__tlittypedlist0)
  | AProj (_t__tlittyped0, _) -> [] @ typed_fv_lit _t__tlittyped0
  | AAppOp (_, _t__tlittypedlist1) ->
      [] @ List.concat (List.map typed_fv_lit _t__tlittypedlist1)

and typed_fv_lit (lit_e : ('t, 't lit) typed) = fv_lit lit_e.x

let rec subst_lit (string_x : string) f (lit_e : 't lit) =
  match lit_e with
  | AC constant0 -> AC constant0
  | AVar _t_stringtyped0 ->
      if String.equal _t_stringtyped0.x string_x then f _t_stringtyped0
      else AVar _t_stringtyped0
  | ATu _t__tlittypedlist0 ->
      ATu (List.map (typed_subst_lit string_x f) _t__tlittypedlist0)
  | AProj (_t__tlittyped0, int1) ->
      AProj (typed_subst_lit string_x f _t__tlittyped0, int1)
  | AAppOp (_t_stringtyped0, _t__tlittypedlist1) ->
      AAppOp
        ( _t_stringtyped0,
          List.map (typed_subst_lit string_x f) _t__tlittypedlist1 )

and typed_subst_lit (string_x : string) f (lit_e : ('t, 't lit) typed) =
  (subst_lit string_x f) #-> lit_e

let rec map_lit : 't 's. ('t -> 's) -> 't lit -> 's lit =
 fun f lit_e ->
  match lit_e with
  | AC constant0 -> AC constant0
  | AVar _t_stringtyped0 -> AVar f #=> _t_stringtyped0
  | ATu _t__tlittypedlist0 ->
      ATu (List.map (fun e -> typed_map_lit f e) _t__tlittypedlist0)
  | AProj (_t__tlittyped0, int1) -> AProj (typed_map_lit f _t__tlittyped0, int1)
  | AAppOp (_t_stringtyped0, _t__tlittypedlist1) ->
      AAppOp
        (f #=> _t_stringtyped0, List.map (typed_map_lit f) _t__tlittypedlist1)

and typed_map_lit :
      't 's. ('t -> 's) -> ('t, 't lit) typed -> ('s, 's lit) typed =
 fun f lit_e -> f #=> ((map_lit f) #-> lit_e)

let fv_lit_id e = fv_typed_id_to_id fv_lit e
let typed_fv_lit_id e = fv_typed_id_to_id typed_fv_lit e
let subst_lit_instance x instance e = subst_f_to_instance subst_lit x instance e

let typed_subst_lit_instance x instance e =
  subst_f_to_instance typed_subst_lit x instance e
(* Generated from _lit.ml *)

(* force *)
let typed_lit_force_aappop_opt (lit, op) =
  match lit.x with
  | AAppOp ({ x; _ }, args) when String.equal x op -> Some args
  | _ -> None

let typed_lit_force_avar_opt lit =
  match lit.x with AVar id -> Some id | _ -> None

let typed_lit_force_ac_opt lit = match lit.x with AC c -> Some c | _ -> None
let mk_true = AC (B true)
let mk_false = AC (B true)

(** For Nt.t typed *)

let mk_lit_eq_lit ty lx ly =
  AAppOp (Op.typed_op_string ty, [ lx #: ty; ly #: ty ])

let mk_var_eq_var ty x y =
  let lx = AVar x in
  let ly = AVar y in
  AAppOp (Op.typed_op_string ty, [ lx #: ty; ly #: ty ])

let mk_int_l1_eq_l2 l1 l2 =
  AAppOp (Op.typed_op_string Nt.Ty_int, [ l1 #: Nt.Ty_int; l2 #: Nt.Ty_int ])

let get_var_opt = function AVar x -> Some x | _ -> None

let get_subst_pair a b =
  match get_var_opt a with Some a -> [ (a, b) ] | None -> []

let get_eqlits lit =
  match lit with
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x ->
      get_subst_pair a.x b.x @ get_subst_pair b.x a.x
  | _ -> []

let find_assignment_of_intvar lit x =
  match lit with
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x -> (
      match (a.x, b.x) with
      | AVar y, _ when String.equal x y.x -> Some b.x
      | _, AVar y when String.equal x y.x -> Some a.x
      | _, _ -> None)
  | _ -> None

let rec get_non_unit_lit lit =
  (* let () = *)
  (*   Env.show_log "gather" @@ fun _ -> *)
  (*   Printf.printf ">>>>> get_non_unit_lit: %s\n" *)
  (*     (Sexplib.Sexp.to_string (sexp_of_lit lit.x)) *)
  (* in *)
  if Nt.equal_nt Nt.Ty_unit lit.ty then None
  else
    match lit.x with
    | AAppOp (_, args) -> (
        (* let () = *)
        (*   Env.show_log "gather" @@ fun _ -> *)
        (*   Printf.printf ">>>>> %s: %s\n" (Op.to_string op.x) *)
        (*     (List.split_by_comma (fun x -> layout x.ty) args) *)
        (* in *)
        let res = List.filter_map get_non_unit_lit args in
        match res with [] -> None | _ -> Some lit.x)
    | _ -> Some lit.x

let get_op_args lit = match lit with AAppOp (_, args) -> args | _ -> []

open Ast
open Zutils
open Prop
(* open Common *)

let layout_sexp_se regex =
  Sexplib.Sexp.to_string @@ sexp_of_sevent (fun _ -> Sexplib.Sexp.unit) regex

(* fv *)

let fv sevent =
  match sevent with
  | GuardEvent { vs; phi } ->
      Zdatatype.List.substract (typed_eq String.equal) ([] @ fv_prop phi) vs
  | EffEvent { vs; phi; _ } ->
      Zdatatype.List.substract (typed_eq String.equal) ([] @ fv_prop phi) vs

(* subst *)

let subst_sevent (y : string) f sevent =
  match sevent with
  | GuardEvent { vs; phi } ->
      if List.exists (fun x -> String.equal x.x y) vs then
        GuardEvent { vs; phi }
      else GuardEvent { vs; phi = subst_prop y f phi }
  | EffEvent { op; vs; phi } ->
      if List.exists (fun x -> String.equal x.x y) vs then
        EffEvent { op; vs; phi }
      else EffEvent { op; vs; phi = subst_prop y f phi }

let subst_sevent_instance y z sevent =
  subst_f_to_instance subst_sevent y z sevent

(* normalize name *)

(* let normalize_name = function *)
(*   | GuardEvent { vs; phi } -> *)
(*       let vs' = vs_names (List.length vs) in *)
(*       let tmp = _safe_combine __FILE__ __LINE__ vs vs' in *)
(*       let phi = *)
(*         List.fold_left *)
(*           (fun phi (x', x) -> subst_prop_instance x'.x (AVar x #: x'.ty) phi) *)
(*           phi tmp *)
(*       in *)
(*       let vs = List.map (fun (x', x) -> x #: x'.ty) tmp in *)
(*       GuardEvent { vs; phi } *)
(*   | EffEvent { op; vs; phi } -> *)
(*       let vs' = vs_names (List.length vs) in *)
(*       let tmp = _safe_combine __FILE__ __LINE__ vs vs' in *)
(*       let phi = *)
(*         List.fold_left *)
(*           (fun phi (x', x) -> subst_prop_instance x'.x (AVar x #: x'.ty) phi) *)
(*           phi tmp *)
(*       in *)
(*       let vs = List.map (fun (x', x) -> x #: x'.ty) tmp in *)
(*       EffEvent { op; vs; phi } *)

(* gather lits *)
(** For Nt.t typed*)

let mk_top_sevent (op : string) l =
  (* let argsty = List.map snd @@ Nt.get_record_types ty in *)
  let vs = List.map (fun (x, ty) -> x #: ty) l in
  (* let vs = vs_names (List.length argsty) in *)
  (* let vs = List.map (fun (x, ty) -> x #: ty) @@ List.combine vs argsty in *)
  (* let vs = (__server_feild #: server_type) :: vs in *)
  (* normalize_name @@ *)
  EffEvent { op; vs; phi = mk_true }

open Zdatatype

type gathered_lits = {
  global_lits : Nt.t lit list;
  local_lits : ((Nt.t, string) typed list * Nt.t lit list) StrMap.t;
}

let gathered_lits_init () = { global_lits = []; local_lits = StrMap.empty }

let gathered_rm_dup { global_lits; local_lits } =
  let global_lits = List.slow_rm_dup Lit.eq_lit global_lits in
  let local_lits =
    StrMap.map
      (fun (vs, lits) -> (vs, List.slow_rm_dup Lit.eq_lit lits))
      local_lits
  in
  { global_lits; local_lits }

let gather_se { global_lits; local_lits } sevent =
  (* let () = Env.show_log "gather" @@ fun _ -> Printf.printf ">>>>> gather:\n" in *)
  match sevent with
  | GuardEvent _ ->
      _die [%here]
      (* { global_lits = Prop.get_lits phi @ global_lits; local_lits } *)
  | EffEvent { op; phi; vs } ->
      let lits = Prop.get_lits phi in
      let vs' = List.map (fun x -> x.x) vs in
      let is_contain_local_free lit =
        match List.interset String.equal vs' @@ Lit.fv_lit_id lit with
        | [] -> false
        | _ -> true
      in
      let llits, glits = List.partition is_contain_local_free lits in
      (* let () = Printf.printf "vs: %s\n" (layout_qvs vs) in *)
      (* let () = *)
      (*   Printf.printf "glits: %s\n" *)
      (*     (List.split_by_comma Lit.layout_sexp_lit glits) *)
      (* in *)
      (* let () = *)
      (*   Printf.printf "llits: %s\n" *)
      (*     (List.split_by_comma Lit.layout_sexp_lit llits) *)
      (* in *)
      (* let () = _die [%here] in *)
      let local_lits =
        StrMap.update op
          (fun l ->
            match l with
            | None -> Some (vs, llits)
            | Some (_, l) -> Some (vs, l @ llits))
          local_lits
      in
      let global_lits = global_lits @ glits in
      { global_lits; local_lits }

let compare_se se1 se2 =
  Sexplib.Sexp.compare
    (sexp_of_sevent Nt.sexp_of_t se1)
    (sexp_of_sevent Nt.sexp_of_t se2)

let and_prop_to_se p = function
  | GuardEvent { phi; vs } -> GuardEvent { phi = smart_add_to p phi; vs }
  | EffEvent { op; phi; vs } -> EffEvent { op; phi = smart_add_to p phi; vs }

let delimit_cotexnt_se = function
  | Some ctx, GuardEvent { phi; _ } -> List.map (and_prop_to_se phi) ctx
  | _, r -> [ r ]

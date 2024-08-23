(* open Common *)

open Syntax
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open To_notation
open To_id
open To_prop

let tpEvent str = spf "⟨%s⟩" str

let pprint = function
  | GuardEvent { vs; phi } ->
      tpEvent
      @@ spf "%s | %s" (List.split_by " " (fun x -> x.x) vs) (layout_prop phi)
  | EffEvent { op; phi; _ } -> tpEvent @@ spf "%s | %s" op (layout_prop phi)
(* spf "%s %s | %s" op *)
(* (List.split_by " " (fun x -> x.x) vs) *)
(* (layout_prop phi) *)

let layout_se = pprint
let layout = pprint
let tpEventRaw str = spf "<%s>" str

let pprintRaw = function
  | GuardEvent { vs; phi } ->
      tpEventRaw
      @@ spf "%s | %s"
           (List.split_by " " (fun x -> x.x) vs)
           (layout_propRaw phi)
  | EffEvent { op; vs; phi } ->
      tpEventRaw
      @@ spf "%s %s | %s" op
           (List.split_by " " (fun x -> x.x) vs)
           (layout_propRaw phi)

let get_opopt expr =
  match To_op.string_to_op_opt (get_denote expr) with
  | Some (DtConstructor op) -> Some (String.uncapitalize_ascii op)
  | _ -> None

let get_op expr = match get_opopt expr with Some x -> x | None -> _die [%here]

let get_self ct =
  match ct.ptyp_desc with
  | Ptyp_extension (name, PTyp ty) -> name.txt #: (Type.core_type_to_t ty)
  | _ ->
      let () = Printf.printf "\nct: %s\n" (Type.layout_ ct) in
      _failatwith __FILE__ __LINE__ ""

let vars_phi_sevent_of_expr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint (e', ct) ->
        let v = get_self ct in
        let vs, phi = aux e' in
        (v :: vs, phi)
    | _ -> ([], prop_of_expr expr)
  in
  let vs, prop = aux expr in
  (List.rev vs, prop)

let desugar_sevent expr =
  match expr.pexp_desc with
  | Pexp_tuple es ->
      let es, ephi =
        match List.last_destruct_opt es with
        | Some (es, ephi) -> (es, ephi)
        | None -> _die [%here]
      in
      let phi = prop_of_expr ephi in
      let es =
        List.map
          (fun e ->
            let x = typed_id_of_expr e in
            match get_denoteopt e with
            | None -> (x, None)
            | Some "d" ->
                let arg = (Rename.unique "x") #: None in
                let arg' = { x = AVar arg; ty = None } in
                let x = { x = AVar x; ty = None } in
                let lit = AAppOp ("==" #: None, [ arg'; x ]) in
                (arg, Some (Lit lit #: (Some Normalty.Ntyped.Ty_bool)))
            | _ -> _die [%here])
          es
      in
      let args = List.map fst es in
      let phis =
        List.fold_left
          (fun res (_, prop) ->
            match prop with None -> res | Some prop -> prop :: res)
          [ phi ] es
      in
      (args, And phis)
  | _ -> _die [%here]

let sevent_of_expr_aux expr =
  match expr.pexp_desc with
  | Pexp_construct (op, Some e) -> (
      (* symbolic operator event *)
      let op = String.uncapitalize_ascii @@ To_id.longid_to_id op in
      match op with
      | "any" ->
          (* symbolic global event *)
          let phi = prop_of_expr e in
          GuardEvent { vs = []; phi }
      | _ ->
          let vs, phi = desugar_sevent e in
          EffEvent { op; vs; phi })
  | _ ->
      let () =
        Printf.printf "unknown symbolic event: %s\n"
        @@ Pprintast.string_of_expression expr
      in
      _die [%here]

let sevent_of_expr expr =
  let rty = sevent_of_expr_aux expr in
  (* let rty = normalize_name rty in *)
  (* let () = Printf.printf "ZZ: %s\n" (pprint_rty rty) in *)
  rty

let of_expr = sevent_of_expr

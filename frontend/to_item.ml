(* open Common *)
open Syntax
open OcamlParser
open Parsetree

(* open Mutils *)
open Zdatatype
(* open To_id *)

let constrant_str = "const"
let inst_str = "machine"

(* type 't ocaml_item = *)
(*   | MTyDecl of type_declaration *)
(*   | MValDecl of ('t, string) typed *)
(*   | MMethodPred of ('t, string) typed *)
(*   | MAxiom of { name : string; prop : 't prop } *)
(*   (\* | MFuncImpRaw of { *\) *)
(*   (\*     name : ('t, string) typed; *\) *)
(*   (\*     if_rec : bool; *\) *)
(*   (\*     body : expression; *\) *)
(*   (\*   } *\) *)
(*   (\* | MFuncImp of { name : ('t, string) typed; if_rec : bool; body : expression } *\) *)
(*   | MAutomataImp of { name : string; automata : expression } *)
(* (\* | MRty of { is_assumption : bool; name : string; rty : expression } *\) *)

let ocaml_structure_item_to_item structure =
  match structure.pstr_desc with
  | Pstr_primitive { pval_name; pval_type; pval_attributes; _ } ->
      Some
        (match pval_attributes with
        | _ -> MValDecl pval_name.txt #: (Nt.core_type_to_t pval_type))
  | Pstr_attribute _ -> None
  | _ ->
      let () =
        Printf.printf "%s\n" (Pprintast.string_of_structure [ structure ])
      in
      _die_with [%here] "translate not a func_decl"

let ocaml_structure_to_items structure =
  List.filter_map ocaml_structure_item_to_item structure

let layout_ct_opt = function Some ct -> Nt.layout ct | None -> _die [%here]
let layout_opt_ty = function None -> "?" | Some t -> Nt.layout t

let layout_opt_item = function
  | MFieldAssign { field; assignment } -> spf "%s = %s" field assignment
  | MAbstractType { x; ty = CEnumType { enum_elems; _ } } ->
      spf "enum %s = %s" x (List.split_by " | " (fun x -> x) enum_elems)
  | MAbstractType { x; ty = CBaseType { superty; _ } } ->
      spf "type %s = %s" x (Nt.layout superty)
  | MEventDecl { ev = x; _ } -> spf "val %s: %s" x.x @@ Nt.layout x.ty
  | MValDecl x -> spf "val %s: %s" x.x @@ Nt.layout x.ty
  | MRegex { name; automata } ->
      spf "spec %s = %s" name.x
        (To_regex.layout layout_opt_ty To_sevent.layout automata)
  | MClient
      { client_name; event_scope; axioms; type_configs; violation; step_bound }
    ->
      let layout_names = List.split_by " " (fun x -> x) in
      spf
        "client %s =\n\
         \tscope [%s]\n\
         \taxiom [%s]\n\
         \tconfig [%s]\n\
         \tviolation %s\n\
         \tstep %i" client_name (layout_names event_scope) (layout_names axioms)
        (layout_names type_configs)
        violation step_bound

let layout_item = function
  | MFieldAssign { field; assignment } -> spf "%s = %s" field assignment
  | MAbstractType { x; ty = CEnumType { enum_elems; _ } } ->
      spf "enum %s = %s" x (List.split_by " | " (fun x -> x) enum_elems)
  | MAbstractType { x; ty = CBaseType { superty; _ } } ->
      spf "type %s = %s" x (Nt.layout superty)
  | MEventDecl { ev = x; _ } -> spf "val %s: %s" x.x @@ Nt.layout x.ty
  | MValDecl x -> spf "val %s: %s" x.x @@ Nt.layout x.ty
  | MRegex { name; automata } ->
      spf "let[@regex] %s = %s" name.x
        (To_regex.layout Nt.layout To_sevent.layout automata)
  | MClient
      { client_name; event_scope; axioms; type_configs; violation; step_bound }
    ->
      let layout_names = List.split_by " " (fun x -> x) in
      spf
        "client %s =\n\
         \tscope [%s]\n\
         \taxiom [%s]\n\
         \tconfig [%s]\n\
         \tviolation %s\n\
         \tstep %i" client_name (layout_names event_scope) (layout_names axioms)
        (layout_names type_configs)
        violation step_bound

let layout_opt_structure l = spf "%s\n" (List.split_by "\n" layout_opt_item l)
let layout_structure l = spf "%s\n" (List.split_by "\n" layout_item l)

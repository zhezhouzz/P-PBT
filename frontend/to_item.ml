open Syntax
open OcamlParser
open Parsetree
open To_rty
open Zdatatype
open AutomataLibrary

let rec parse_goal expr =
  match expr.pexp_desc with
  | Pexp_fun (_, _, pattern, body) ->
      let vs, srl = parse_goal body in
      let v =
        match pattern.ppat_desc with
        | Ppat_constraint (id, ct) ->
            (id_of_pattern id) #: (Nt.core_type_to_t ct)
        | _ -> _die_with [%here] "wrong format"
      in
      (v :: vs, srl)
  | _ -> ([], symbolic_regex_of_expr expr)

let ocaml_structure_item_to_p_event_decl structure =
  match structure.pstr_desc with
  | Pstr_primitive { pval_name; pval_type; _ } ->
      (pval_name.txt, Nt.core_type_to_t pval_type)
  | _ -> _die_with [%here] "wrong format"

let ocaml_structure_item_to_item structure =
  let () =
    _log "parsing" @@ fun _ ->
    Pp.printf "@{<bold>parsing:@}\n%s\n"
      (Pprintast.string_of_structure [ structure ])
  in
  match structure.pstr_desc with
  | Pstr_primitive { pval_name; pval_type; pval_attributes; _ } -> (
      match pval_attributes with
      | [] ->
          Some
            (PrimDecl { name = pval_name.txt; nt = Nt.core_type_to_t pval_type })
      | [ x ] when String.equal x.attr_name.txt "gen" ->
          Some
            (MsgNtDecl
               {
                 name = pval_name.txt;
                 nt = Nt.core_type_to_t pval_type;
                 generative = true;
                 recvable = false;
               })
      | [ x ] when String.equal x.attr_name.txt "obs" ->
          Some
            (MsgNtDecl
               {
                 name = pval_name.txt;
                 nt = Nt.core_type_to_t pval_type;
                 generative = false;
                 recvable = false;
               })
      | [ x ] when String.equal x.attr_name.txt "obsRecv" ->
          Some
            (MsgNtDecl
               {
                 name = pval_name.txt;
                 nt = Nt.core_type_to_t pval_type;
                 generative = false;
                 recvable = true;
               })
      | _ -> _die [%here])
  | Pstr_value (_, [ value_binding ]) ->
      Some
        (let name = id_of_pattern value_binding.pvb_pat in
         match value_binding.pvb_attributes with
         | [] -> MsgDecl { name; haft = haft_of_expr value_binding.pvb_expr }
         | [ x ] -> (
             match x.attr_name.txt with
             | "goal" ->
                 let qvs, prop = parse_goal value_binding.pvb_expr in
                 SynGoal { qvs; prop }
             | _ ->
                 _die_with [%here]
                   "syntax error: non known rty kind, not axiom | assert | \
                    library")
         | _ -> _die [%here])
  | Pstr_attribute _ -> None
  | _ ->
      let () =
        Printf.printf "%s\n" (Pprintast.string_of_structure [ structure ])
      in
      _die_with [%here] "translate not a func_decl"

let ocaml_structure_to_items structure =
  List.filter_map ocaml_structure_item_to_item structure

let ocaml_structure_to_p_tyctx structure =
  StrMap.from_kv_list @@ List.map ocaml_structure_item_to_p_event_decl structure

let layout_syn_goal { qvs; prop } =
  spf "%s.%s"
    (List.split_by "." (fun x -> spf "∀%s" @@ layout_qv x) qvs)
    (layout_symbolic_regex prop)

let layout_item = function
  | MsgNtDecl { generative; recvable; name; nt } ->
      spf "%s %s: %s"
        (if generative then "gen" else if recvable then "obsRecv" else "obs")
        name (Nt.layout nt)
  | PrimDecl { name; nt } -> spf "val %s: %s" name (Nt.layout nt)
  | MsgDecl { name; haft } ->
      spf "rty %s:\n  %s" name (layout_haft layout_symbolic_regex haft)
  | SynGoal g -> spf "goal:\n  %s" (layout_syn_goal g)

let layout_structure l = spf "%s\n" (List.split_by "\n" layout_item l)

let locally_rename_item ctx item =
  let () =
    _log "parsing" @@ fun _ ->
    Pp.printf "@{<bold>parsing2:@}\n%s\n" (layout_item item)
  in
  match item with
  | MsgNtDecl _ | PrimDecl _ -> item
  | MsgDecl { name; haft } ->
      MsgDecl { name; haft = locally_rename_haft ctx haft }
  | SynGoal { qvs; prop } ->
      let prop = locally_rename (ctx_to_list ctx) prop in
      SynGoal { qvs; prop }

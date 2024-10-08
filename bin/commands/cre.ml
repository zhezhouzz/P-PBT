open Caux
open Language
open Ntypecheck
open OcamlParser
open Zdatatype

let parse = Oparse.parse_imp_from_file

let read_ocaml_file source_file () =
  let code = Oparse.parse_imp_from_file ~sourcefile:source_file in
  let code = ocaml_structure_to_items code in
  code

let read_source_file source_file () =
  let postfix = List.last @@ Core.String.split source_file ~on:'.' in
  match postfix with
  | "ml" -> read_ocaml_file source_file ()
  | "s" -> FrontSpec.parse source_file
  | "p" -> FrontSpec.parse source_file
  | _ -> failwith @@ spf "wrong file extension *.%s" postfix

let read_functional_p_file source_file () =
  let postfix = List.last @@ Core.String.split source_file ~on:'.' in
  match postfix with
  | "funcp" -> FrontFuncP.parse source_file
  | _ -> failwith @@ spf "wrong file extension *.%s" postfix

let read_p source_file () =
  let code = read_functional_p_file source_file () in
  let code = Ptypecheck.p_items_infer emp code in
  ()

let load_p_client_machine_template () =
  let header =
    Ptypecheck.p_items_infer emp
      (read_functional_p_file (Myconfig.get_prim_path ()).p_header_template_path
         ())
  in
  let pclient =
    Ptypecheck.p_items_infer emp
      (read_functional_p_file (Myconfig.get_prim_path ()).p_client_template_path
         ())
  in
  let pclient =
    List.nth
      (List.filter_map
         (function PMachine decl -> Some decl | _ -> None)
         pclient)
      0
  in
  (header, pclient)

let register_p_header header spec_tyctx =
  let header = Dequantified.file_register_abstract_types spec_tyctx header in
  let header = Dequantified.file_register_events spec_tyctx header in
  header

let compile_to_p_client pclient client =
  let pclient = Dequantified.machine_register_qtypes client pclient in
  let pclient = Dequantified.machine_register_automata client pclient in
  { pclient with name = client.client_name }

let compile_to_p_program (spec_tyctx, clients) output_file () =
  let open SymExplore in
  let header, pclient = load_p_client_machine_template () in
  let pclients = List.map (compile_to_p_client pclient) clients in
  let pcode = List.map (fun decl -> PMachine decl) pclients in
  let () =
    Printf.fprintf
      (Core.Out_channel.create ~fail_if_exists:false ~append:false output_file)
      "%s\n"
      (layout_p_program spec_tyctx pcode)
  in
  ()

let get_typed_spec p_header_file spec_source_file =
  let predefined_code =
    read_source_file (Myconfig.get_prim_path ()).predefined_path ()
  in
  let header_code = FrontWrapper.parse p_header_file in
  let reqresp_ctx = code_to_reqresp_ctx header_code in
  let env, simp_env, code = simplify_wrapper header_code header_code in
  let enum_names =
    List.filter_map
      (function WrapperEnum { enum_name; _ } -> Some enum_name | _ -> None)
      code
  in
  let tab = mk_wrappers enum_names (env, simp_env, header_code) in
  let wrapper_ctx = tab_to_wrapper_ctx tab in
  let header = code_to_items header_code in
  let code = read_source_file spec_source_file () in
  let spec_ctx =
    mk_spec_ctx (env, wrapper_ctx, reqresp_ctx) (predefined_code @ header @ code)
  in
  let code = struct_check spec_ctx code in
  (spec_ctx, code)

let read_p_and_spec p_header_file spec_source_file output_file () =
  let spec_ctx, code = get_typed_spec p_header_file spec_source_file in
  let () = Printf.printf "%s\n" @@ layout_structure code in
  let client_ctx = Instantiate.inst_client spec_ctx code in
  (* let () = _die [%here] in *)
  let clients =
    List.map (fun x ->
        let client = x.ty in
        let () = Printf.printf "original:\n" in
        let () = Instantiate.print_transsfa_client_violation client in
        let () =
          Printf.printf
            "add counting properties: e.g., number of request is greater than \
             number of response along the path\n"
        in
        let client = SymExplore.test__dfa_with_bound client in
        let () = Printf.printf "explored:\n" in
        let () = Instantiate.print_strsfa_client_violation client in
        (* let () = Instantiate.print_transsfa_client_violation client in *)
        (* let client = SymExplore.refine_client client in *)
        (* let () = Printf.printf "refined:\n" in *)
        (* let () = Instantiate.print_transsfa_client_violation client in *)
        let client = SymExplore.rule_out_hidden client in
        let () = Printf.printf "filtered:\n" in
        let () = Instantiate.print_strsfa_client_violation client in
        let () = Instantiate.print_transsfa_client_violation client in
        (* let () = _die [%here] in *)
        client)
    @@ ctx_to_list client_ctx
  in
  compile_to_p_program (spec_ctx, clients) output_file ()

let random_read_p_and_spec p_header_file spec_source_file output_file () =
  let spec_ctx, code = get_typed_spec p_header_file spec_source_file in
  let () = Printf.printf "%s\n" @@ layout_structure code in
  let client_ctx = Instantiate.inst_client spec_ctx code in
  (* let () = _die [%here] in *)
  let clients =
    List.map (fun x ->
        let client = x.ty in
        let () = Printf.printf "original:\n" in
        let () = Instantiate.print_transsfa_client_violation client in
        let client = SymExplore.rule_out_hidden client in
        let () = Printf.printf "filtered:\n" in
        let () = Instantiate.print_strsfa_client_violation client in
        let () = Instantiate.print_transsfa_client_violation client in
        (* let () = _die [%here] in *)
        client)
    @@ ctx_to_list client_ctx
  in
  compile_to_p_program (spec_ctx, clients) output_file ()

let read_automata source_file () =
  let code = read_source_file source_file () in
  ()

let read_sfa source_file () =
  let code = read_source_file source_file () in
  let () = Printf.printf "%s\n" @@ layout_opt_structure code in
  ()

let read_p_repo_aux source_path =
  let p_paths =
    List.filter (fun path ->
        let postfix = List.last @@ Core.String.split path ~on:'.' in
        match postfix with "p" | "s" -> true | _ -> false)
    @@ dir_contents source_path
  in
  let error_files = ref [] in
  let code =
    List.concat_map
      (fun file ->
        (* let () = Printf.printf "parsing %s\n" file in *)
        try FrontWrapper.parse file
        with Failure msg ->
          let () =
            Printf.printf "Cannot parse file %s, skip it.\n%s\n" file msg
          in
          let () = error_files := file :: !error_files in
          [])
      p_paths
  in
  let () =
    match !error_files with
    | [] -> ()
    | l ->
        Pp.printf
          "@{<yellow>The following files cannot be parsed, are skipped:@}\n%s\n"
        @@ List.split_by "\n" (fun x -> x) l
  in
  let code = List.filter is_p_type_event code in
  code

let read_p_repo source_path () =
  let code = read_p_repo_aux source_path in
  let () = Printf.printf "%s\n" (Backend.layout_p_wapper_decls code) in
  ()

let p_wrapper source_path header_spec_file () =
  let code = read_p_repo_aux source_path in
  let header_spec =
    List.filter is_spec @@ FrontWrapper.parse header_spec_file
  in
  let () = Printf.printf "%s\n" (Backend.layout_p_wapper_decls code) in
  let env, simp_env, code = simplify_wrapper code header_spec in
  let () =
    Printf.printf "Sinmpified\n\n%s\n" (Backend.layout_p_wapper_decls code)
  in
  (* let () = _die [%here] in *)
  let enum_names =
    List.filter_map
      (function WrapperEnum { enum_name; _ } -> Some enum_name | _ -> None)
      code
  in
  let tab = mk_wrappers enum_names (env, simp_env, header_spec) in
  let () =
    Printf.printf "\n%s\n" (to_conversion_code (code, header_spec, tab))
  in
  (* let () = *)
  (*   Printf.printf "Sinmpified\n%s\n" (Backend.layout_p_wapper_decls code) *)
  (* in *)
  ()

let two_param message f =
  Command.basic ~summary:message
    Command.Let_syntax.(
      let%map_open config_file =
        flag "config"
          (optional_with_default Myconfig.default_meta_config_path regular_file)
          ~doc:"config file path"
      and file1 = anon ("file1" %: regular_file)
      and source_file = anon ("source_code_file" %: regular_file) in
      let () = Myconfig.meta_config_path := config_file in
      f file1 source_file)

let three_param message f =
  Command.basic ~summary:message
    Command.Let_syntax.(
      let%map_open config_file =
        flag "config"
          (optional_with_default Myconfig.default_meta_config_path regular_file)
          ~doc:"config file path"
      and file1 = anon ("file2" %: regular_file)
      and file2 = anon ("file3" %: string)
      and file3 = anon ("file3" %: string) in
      let () = Myconfig.meta_config_path := config_file in
      f file1 file2 file3)

let one_param message f =
  Command.basic ~summary:message
    Command.Let_syntax.(
      let%map_open config_file =
        flag "config"
          (optional_with_default Myconfig.default_meta_config_path regular_file)
          ~doc:"config file path"
      and source_file = anon ("source_code_file" %: regular_file) in
      let () = Myconfig.meta_config_path := config_file in
      f source_file)

let one_param_string message f =
  Command.basic ~summary:message
    Command.Let_syntax.(
      let%map_open config_file =
        flag "config"
          (optional_with_default Myconfig.default_meta_config_path regular_file)
          ~doc:"config file path"
      and source_file = anon ("source_code_file" %: string) in
      let () = Myconfig.meta_config_path := config_file in
      f source_file)

let two_param_string message f =
  Command.basic ~summary:message
    Command.Let_syntax.(
      let%map_open config_file =
        flag "config"
          (optional_with_default Myconfig.default_meta_config_path regular_file)
          ~doc:"config file path"
      and file1 = anon ("file1" %: string)
      and source_file = anon ("source_code_file" %: regular_file) in
      let () = Myconfig.meta_config_path := config_file in
      f file1 source_file)

let cmds =
  [
    ("read-automata", one_param "read_automata" read_automata);
    ("read-sfa", one_param "read_sfa" read_sfa);
    ("read-p", one_param "read_p" read_p);
    ("read-p-sfa", three_param "read_p" read_p_and_spec);
    ("random-p-sfa", three_param "read_p" random_read_p_and_spec);
    ("read-p-wrapper", two_param_string "p-wrapper" p_wrapper);
    ("read-p-repo", one_param_string "p-wrapper" read_p_repo);
  ]

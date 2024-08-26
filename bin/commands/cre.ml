open Core
open Caux
open Language
open Zzdatatype.Datatype
open Ntypecheck

let parse = Ocaml5_parser.Frontend.parse

let read_ocaml_file source_file () =
  let code = Ocaml5_parser.Frontend.parse ~sourcefile:source_file in
  let code = ocaml_structure_to_items code in
  code

let read_source_file source_file () =
  let postfix = List.last @@ String.split source_file ~on:'.' in
  match postfix with
  | "ml" -> read_ocaml_file source_file ()
  | "s" -> FrontSpec.parse source_file
  | "p" -> FrontSpec.parse source_file
  | _ -> failwith @@ spf "wrong file extension *.%s" postfix

let read_functional_p_file source_file () =
  let postfix = List.last @@ String.split source_file ~on:'.' in
  match postfix with
  | "funcp" -> FrontFuncP.parse source_file
  | _ -> failwith @@ spf "wrong file extension *.%s" postfix

let read_p source_file () =
  let code = read_functional_p_file source_file () in
  let code = Ptypecheck.p_items_infer emp code in
  (* let code = map_on_p_machine Dequantified.machine_register_qtypes_test code in *)
  (* let () = Printf.printf "%s\n" (layout_p_program code) in *)
  (* let code = map_on_p_machine Dequantified.machine_register_world_test code in *)
  (* let () = Printf.printf "%s\n" (layout_p_program code) in *)
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
  (* let header = register_p_header header spec_tyctx in *)
  let pclients = List.map (compile_to_p_client pclient) clients in
  let pcode = List.map (fun decl -> PMachine decl) pclients in
  (* let code = read_functional_p_file p_source_file () in *)
  (* let code = Ptypecheck.p_items_infer emp code in *)
  (* let code = Dequantified.file_register_events client.spec_tyctx code in *)
  (* let code = *)
  (*   map_on_p_machine *)
  (*     (fun m -> Dequantified.machine_register_qtypes client.spec_tyctx m) *)
  (*     code *)
  (* in *)
  (* (\* let regspec = { world = sym_ctx.world; reg = [ (mk_true, pautomata) ] } in *\) *)
  (* (\* let code = *\) *)
  (* (\*   map_on_p_machine *\) *)
  (* (\*     (fun m -> Dequantified.machine_register_automata sym_ctx m regspec) *\) *)
  (* (\*     code *\) *)
  (* (\* in *\) *)
  let () =
    Printf.fprintf
      (Out_channel.create ~fail_if_exists:false ~append:false output_file)
      "%s\n"
      (layout_p_program spec_tyctx pcode)
  in
  ()

let get_typed_spec p_header_file spec_source_file =
  let predefined_code =
    read_source_file (Myconfig.get_prim_path ()).predefined_path ()
  in
  let header_code = FrontWrapper.parse p_header_file in
  (* let () = *)
  (*   Printf.printf "Sinmpified\n%s\n" (Backend.layout_p_wapper_decls header_code) *)
  (* in *)
  let reqresp_ctx = code_to_reqresp_ctx header_code in
  let env, simp_env, code = simplify_wrapper header_code header_code in
  let tab = mk_wrappers (env, simp_env, header_code) in
  let wrapper_ctx = tab_to_wrapper_ctx tab in
  (* let () = *)
  (*   Printf.printf "\n%s\n" (to_conversion_code (code, header_code, tab)) *)
  (* in *)
  (* let _ = _die [%here] in *)
  let header = code_to_items header_code in
  let code = read_source_file spec_source_file () in
  let spec_ctx =
    mk_spec_ctx (wrapper_ctx, reqresp_ctx) (predefined_code @ header @ code)
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
        let () = Instantiate.print_strsfa_client client in
        let () =
          Printf.printf
            "add counting properties: e.g., number of request is greater than \
             number of response along the path\n"
        in
        let client = SymExplore.test__dfa_with_bound client in
        let () = Printf.printf "explored:\n" in
        let () = Instantiate.print_strsfa_client_violation client in
        let client = SymExplore.refine_client client in
        let () = Printf.printf "refined:\n" in
        let () = Instantiate.print_strsfa_client_violation client in
        (* let () = Instantiate.print_sfa_client_violation client in *)
        (* let () = _die [%here] in *)
        let client = SymExplore.rule_out_hidden client in
        let () = Printf.printf "filtered:\n" in
        let () = Instantiate.print_strsfa_client_violation client in
        (* let () = Instantiate.print_sfa_client_violation client in *)
        (* let () = _die [%here] in *)
        client)
    @@ ctx_to_list client_ctx
  in
  (* let client = _get_force __FILE__ __LINE__ client_ctx "client1" in *)
  (* let () = *)
  (*   Printf.printf "%i is mem of dfa?: %b\n" 6 *)
  (*     (StateMap.mem 6 (snd @@ List.nth client.violation 0).next) *)
  (* in *)
  (* let sfa = Instantiate.regspec_to_sfa Desymbolic.OriginalFA sfa in *)
  (* let sfa = Instantiate.rename_regspec_by_event_ctx spec_ctx sfa in *)
  (* let sym_ctx = *)
  (*   SymExplore.init_explore_ctx ~spec_ctx ~world:sfa.world ~request_bound:4 *)
  (*     ~step_bound:6 *)
  (* in *)
  (* let sym_ctx = *)
  (*   SymExplore.init_dummy_ctx ~event_tyctx ~event_kindctx ~world:sfa.world *)
  (*     ~request_bound:4 ~step_bound:5 *)
  (* in *)
  (* let () = Printf.printf "Ctx:\n%s\n" @@ SymExplore.layout_ctx sym_ctx in *)
  (* let dfa_list = sfa.reg in *)
  (* let sgnal = *)
  (*   StrAutomata.display_dfa @@ symbolic_dfa_to_event_name_dfa (snd dfa) *)
  (* in *)
  (* let () = *)
  (*   Printf.printf *)
  (* "add counting properties: e.g., number of request is greater than number \ *)
     (*      of response along the path\n" *)
  (* in *)
  (* let client' = SymExplore.test__dfa_with_bound client in *)
  (* let () = Instantiate.print_strsfa_client client' in *)
  (* let () = _die [%here] in *)
  compile_to_p_program (spec_ctx, clients) output_file ()

(* let () = failwith "die" in *)
(* let dfa, dfa_list = *)
(*   match client.violation with *)
(*   | dfa :: dfa_list -> (dfa, dfa_list) *)
(*   | _ -> _die [%here] *)
(* in *)
(* let ptree = SymExplore.explore_counterexample_paths client dfa in *)
(* let () = _die [%here] in *)
(* (\* HACK: time consuming *\) *)
(* (\* let ptree = *\) *)
(* (\*   List.fold_right *\) *)
(* (\*     (fun dfa res -> *\) *)
(* (\*       match SymExplore.bfs_with_filter_and_ptree sym_ctx dfa res with *\) *)
(* (\*       | None -> _die [%here] *\) *)
(* (\*       | Some res -> *\) *)
(* (\*           let () = *\) *)
(* (\*             Printf.printf "sizeof(tree) = %i\n" (SymExplore.num_pnode res) *\) *)
(* (\*           in *\) *)
(* (\*           let () = _die [%here] in *\) *)
(* (\*           res) *\) *)
(* (\*     dfa_list ptree *\) *)
(* (\* in *\) *)
(* let pautomata = SymExplore.pathtree_to_automata ptree in *)
(* let pautomata = SFA.minimize pautomata in *)
(* let pautomata = SFA.unionify_sevent pautomata in *)
(* (\* let sgnal = SFA.display_dfa pautomata in *\) *)
(* let sgnal = *)
(*   StrAutomata.display_dfa @@ symbolic_dfa_to_event_name_dfa pautomata *)
(* in *)
(* (\* let () = failwith "die" in *\) *)
(* compile_to_p_program (client, pautomata) p_source_file output_file () *)

(* let get_sfa_by_name code n = *)
(*   let tmp = *)
(*     List.filter_map *)
(*       (function *)
(*         | MRegex { name; automata } -> *)
(*             if String.equal name.x n then Some (get_regex_from_qregex automata) *)
(*             else None *)
(*         | _ -> None) *)
(*       code *)
(*   in *)
(*   List.nth tmp 0 *)

(* let test_fa2 code = *)
(*   let open StrAutomata in *)
(*   let a1 = get_fa_by_name code "a1" in *)
(*   let b1 = get_fa_by_name code "b1" in *)
(*   let nfa1 = compile [ "a"; "b" ] a1 in *)
(*   let nfa2 = compile [] b1 in *)
(*   let () = *)
(*     print_endline "NFA1: "; *)
(*     layout_nfa nfa1 *)
(*   in *)
(*   let () = *)
(*     print_endline "NFA2: "; *)
(*     layout_nfa nfa2 *)
(*   in *)
(*   let dfa1 = minimize @@ determinize @@ compile [ "a"; "b" ] a1 in *)
(*   let dfa2 = minimize @@ determinize @@ compile [] b1 in *)
(*   let () = *)
(*     print_endline "DFA1: "; *)
(*     layout_dfa dfa1 *)
(*   in *)
(*   let () = *)
(*     print_endline "DFA2: "; *)
(*     layout_dfa dfa2 *)
(*   in *)
(*   let dfa12 = intersect_dfa dfa1 dfa2 in *)
(*   let () = *)
(*     print_endline "DFA1 intersect DFA2: "; *)
(*     layout_dfa dfa12 *)
(*   in *)
(*   let dfa12 = minimize dfa12 in *)
(*   let () = *)
(*     print_endline "DFA1 intersect DFA2: "; *)
(*     layout_dfa dfa12 *)
(*   in *)
(*   () *)

(* let test_fa3 code = *)
(*   let open StrAutomata in *)
(*   let a1 = get_fa_by_name code "a1" in *)
(*   let a1 = delimit_context @@ desugar a1 in *)
(*   let m = index_regex a1 in *)
(*   let a1' = to_index_regex m a1 in *)
(*   let module IdA = IdAutomata in *)
(*   let dfa1 = IdA.compile2dfa a1' in *)
(*   let dfa1_dot = IdA.digraph_of_nfa (IdA.inject dfa1) in *)
(*   let () = Format.printf "%a@." format_digraph dfa1_dot in *)
(*   () *)

let read_automata source_file () =
  let code = read_source_file source_file () in
  (* let () = Printf.printf "%s\n" @@ layout_opt_structure code in *)
  (* let _, code = struct_check emp code in *)
  (* let () = Printf.printf "%s\n" @@ layout_structure code in *)
  (* let () = test_fa3 code in *)
  ()

(* let test_sfa1 code = *)
(*   let srl = get_sfa_by_name code "poly_spec" in *)
(*   let srl = delimit_context @@ desugar srl in *)
(*   let bmap, rl = Desymbolic.desymbolic (fun _ -> true) srl in *)
(*   let () = Printf.printf "%s\n" @@ layout_desym_regex rl in *)
(*   let module DFA = DesymFA in *)
(*   let fa = DFA.compile2dfa rl in *)
(*   (\* let () = DFA.save_as_digraph fa "tmp.dot" in *\) *)
(*   let sfa = SFA.from_desym_dfa bmap fa in *)
(*   let () = Printf.printf "%s\n" @@ SFA.layout_dfa sfa in *)
(*   let () = SFA.save_as_digraph sfa "tmp.dot" in *)
(*   () *)

let read_sfa source_file () =
  let code = read_source_file source_file () in
  let () = Printf.printf "%s\n" @@ layout_opt_structure code in
  (* let _, code = struct_check emp code in *)
  (* let () = Printf.printf "%s\n" @@ layout_structure code in *)
  (* let machines = Instantiate.eta_reduction_items emp code in *)
  (* let machines = *)
  (*   StrMap.of_seq @@ List.to_seq *)
  (*   @@ List.filter_map (fun x -> *)
  (*          let* m = Instantiate.regex_expr_to_machine_opt x.ty in *)
  (*          Some (x.x, m)) *)
  (*   @@ ctx_to_list machines *)
  (* in *)
  (* let () = *)
  (*   StrMap.iter *)
  (*     (fun name m -> *)
  (*       Printf.printf "machine %s:\n%s\n" name *)
  (*       @@ Instantiate.layout_symbolic_machine m) *)
  (*     machines *)
  (* in *)
  (* let machines = Instantiate.machines_to_sfas Desymbolic.OriginalFA machines in *)
  (* let machine = StrMap.find "die" machines "client" in *)
  (* let () = *)
  (*   StrMap.iter *)
  (*     (fun name m -> *)
  (*       let () = *)
  (*         Printf.printf "machine %s:\n%s\n" name *)
  (*         @@ Instantiate.layout_sfa_machine m *)
  (*       in *)
  (*       let () = SFA.save_as_digraph m.reg "tmp.dot" in *)
  (*       ()) *)
  (*     machines *)
  (* in *)
  (* let () = test_sfa1 code in *)
  ()

let read_p_repo source_path () =
  let p_paths =
    List.filter (fun path ->
        let postfix = List.last @@ String.split path ~on:'.' in
        match postfix with "p" -> true | _ -> false)
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
  let () = Printf.printf "%s\n" (Backend.layout_p_wapper_decls code) in
  ()

let p_wrapper source_path header_spec_file () =
  let p_paths =
    List.filter (fun path ->
        let postfix = List.last @@ String.split path ~on:'.' in
        match postfix with "p" -> true | _ -> false)
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
  let () = Printf.printf "%s\n" (Backend.layout_p_wapper_decls code) in
  let () =
    match !error_files with
    | [] -> ()
    | l ->
        Pp.printf
          "@{<yellow>The following files cannot be parsed, are skipped:@}\n%s\n"
        @@ List.split_by "\n" (fun x -> x) l
  in
  let header_spec = FrontWrapper.parse header_spec_file in
  let env, simp_env, code = simplify_wrapper code header_spec in
  (* let env, code = code_reduction env code in *)
  let tab = mk_wrappers (env, simp_env, header_spec) in
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
    ("read-p-wrapper", two_param_string "p-wrapper" p_wrapper);
    ("read-p-repo", one_param_string "p-wrapper" read_p_repo);
  ]

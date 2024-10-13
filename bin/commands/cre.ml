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
  (* | "s" -> FrontSpec.parse source_file *)
  (* | "p" -> FrontSpec.parse source_file *)
  | _ -> failwith @@ spf "wrong file extension *.%s" postfix

let read_functional_p_file source_file () =
  let postfix = List.last @@ Core.String.split source_file ~on:'.' in
  match postfix with
  (* | "funcp" -> FrontFuncP.parse source_file *)
  | _ -> failwith @@ spf "wrong file extension *.%s" postfix

(* let read_p source_file () = *)
(*   let code = read_functional_p_file source_file () in *)
(*   let code = Ptypecheck.p_items_infer emp code in *)
(*   () *)

let read_syn source_file () =
  let code = read_source_file source_file () in
  (* let () = Printf.printf "%s\n" (layout_structure code) in *)
  let env = Ntypecheck.(struct_check init_env code) in
  let () = Printf.printf "%s\n" (layout_syn_env env) in
  let term = Synthesis.syn_one env in
  ()

let syn_term source_file output_file () =
  let code = read_source_file source_file () in
  (* let () = Printf.printf "%s\n" (layout_structure code) in *)
  let env = Ntypecheck.(struct_check init_env code) in
  let () = Printf.printf "%s\n" (layout_syn_env env) in
  let term = Synthesis.syn_one env in
  let oc = Out_channel.open_text output_file in
  try
    Sexplib.Sexp.output oc @@ sexp_of_term term;
    Out_channel.close oc
  with e ->
    Out_channel.close oc;
    raise e

let eval source_file output_file () =
  let code = read_source_file source_file () in
  let env = Ntypecheck.(struct_check init_env code) in
  let () = Printf.printf "%s\n" (layout_syn_env env) in
  let ic = In_channel.open_text output_file in
  let sexp = Sexplib.Sexp.load_sexp output_file in
  let term = term_of_sexp sexp in
  let () = Interpreter.interpret env term in
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
      and source_file = anon ("source_code_file" %: regular_file)
      and file1 = anon ("file1" %: string) in
      let () = Myconfig.meta_config_path := config_file in
      f source_file file1)

let cmds =
  [
    ("read-syn", one_param "read_syn" read_syn);
    ("syn-one", two_param_string "syn-one" syn_term);
    ("eval", two_param_string "eval" eval);
    (* ("read-automata", one_param "read_automata" read_automata); *)
    (* ("read-sfa", one_param "read_sfa" read_sfa); *)
    (* ("read-p", one_param "read_p" read_p); *)
    (* ("read-p-sfa", three_param "read_p" read_p_and_spec); *)
    (* ("random-p-sfa", three_param "read_p" random_read_p_and_spec); *)
    (* ("read-p-wrapper", two_param_string "p-wrapper" p_wrapper); *)
    (* ("read-p-repo", one_param_string "p-wrapper" read_p_repo); *)
  ]

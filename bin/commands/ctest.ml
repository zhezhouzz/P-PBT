open Core
open Caux
open Language
open Ntypecheck

let test_compile_raw_regex_to_dfa f =
  Command.basic ~summary:"test compile raw regex to dfa"
    Command.Let_syntax.(
      let%map_open config_file =
        flag "config"
          (optional_with_default Myconfig.default_meta_config_path regular_file)
          ~doc:"config file path"
      and num_regex = anon ("num-regex" %: int)
      and times = anon ("times" %: int) in
      let () = Myconfig.meta_config_path := config_file in
      fun () -> Zutils._assert [%here] "test" @@ f num_regex times)

let cmds =
  [
    ( "test-reg-fa-1",
      test_compile_raw_regex_to_dfa QcFa.qc_test_compile_raw_regex_to_dfa_1 );
    ( "test-reg-fa-2",
      test_compile_raw_regex_to_dfa QcFa.qc_test_compile_raw_regex_to_dfa_2 );
    ( "test-fa-minimalize",
      test_compile_raw_regex_to_dfa QcFa.qc_test_fa_minimalize );
    ( "test-fa-normalize",
      test_compile_raw_regex_to_dfa QcFa.qc_test_fa_normalize );
    ("test-fa-complete", test_compile_raw_regex_to_dfa QcFa.qc_test_fa_complete);
    ( "test-fa-complement",
      test_compile_raw_regex_to_dfa QcFa.qc_test_fa_complement );
    ( "test-fa-intersection",
      test_compile_raw_regex_to_dfa QcFa.qc_test_fa_intersection );
    ("test-fa-union", test_compile_raw_regex_to_dfa QcFa.qc_test_fa_union);
  ]

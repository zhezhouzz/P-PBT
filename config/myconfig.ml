open MyconfigAst

let default_meta_config_path = "meta-config.json"
let meta_config_path = ref default_meta_config_path
let meta_config : meta_config option ref = ref None

let get_meta () =
  match !meta_config with
  | Some config -> config
  | None ->
      let config_json = Yojson.Safe.from_file !meta_config_path in
      let config =
        match meta_config_of_yojson config_json with
        | Error str ->
            Printf.printf "Meta Config Parsing Error:\n\t%s\n" str;
            failwith "die"
        | Ok c -> normalize_config c
      in
      let () = meta_config := Some config in
      config

let get_mode () = (get_meta ()).mode
let get_max_printing_size () = (get_meta ()).max_printing_size
let get_log_tags () = (get_meta ()).log_tags
let get_prover_timeout_bound () = (get_meta ()).prover_timeout_bound

let _log kw (f : unit -> unit) =
  match get_log_tags () with
  | l when List.exists (String.equal kw) l -> f ()
  | _ -> ()

let _log_preprocess = _log "preprocess"
let _log_result = _log "result"
let _log_typing = _log "typing"
let _log_queries = _log "queries"
let _log_minterms = _log "minterms"
let _log_solving = _log "solving"
let _log_stat = _log "stat"
let _log_info = _log "info"
let _log_debug = _log "debug"
let get_prim_path () = (get_meta ()).prim_path

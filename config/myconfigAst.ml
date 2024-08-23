type mode = Debug | Release [@@deriving yojson]

type preload_path = {
  predefined_path : string;
  axioms_path : string;
  templates_path : string;
  p_header_template_path : string;
  p_client_template_path : string;
}
[@@deriving yojson]

type meta_config = {
  log_tags : string list;
  mode : mode;
  max_printing_size : int;
  prim_path : preload_path;
  prover_timeout_bound : int;
}
[@@deriving yojson]

let normalize_config c =
  match c.mode with Release -> { c with log_tags = [] } | Debug -> c

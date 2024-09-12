open Sexplib.Std
open Zutils
open Prop
open AutomataLibrary
open Constructor_declaration
open Common

type event_kind = Req | Resp | Hidden [@@deriving sexp, show, eq, ord]

type concrete_type =
  | CBaseType of { superty : Nt.nt; use_config : bool }
  | CEnumType of { enum_name : string; enum_elems : string list }
    (* enum type *)
[@@deriving sexp, show, eq, ord]

let concrete_type_to_nt = function
  | CBaseType { superty; _ } -> superty
  | CEnumType { enum_name; _ } -> mk_p_abstract_ty enum_name

type client_field =
  | StepBound of int
  | EventScope of string list
  | Axioms of string list
  | TypeConfigs of string list
  | Violation of string
[@@deriving sexp, show, eq, ord]

type client_setting = {
  client_name : string;
  step_bound : int;
  event_scope : string list;
  axioms : string list;
  type_configs : string list;
  violation : string;
}
[@@deriving sexp, show, eq, ord]

type 't item =
  | MFieldAssign of { field : string; assignment : string }
  | MValDecl of (Nt.nt, string) typed
  | MAbstractType of (concrete_type, string) typed
  | MEventDecl of { ev : (Nt.nt, string) typed; event_kind : event_kind }
  | MRegex of { name : (Nt.nt, string) typed; automata : ('t, 't sevent) regex }
  | MClient of client_setting
[@@deriving sexp, show, eq, ord]

let deparse_field = Sugar.spf "%s.%s"

let parse_client name fields =
  let setting =
    ref
      {
        client_name = name;
        step_bound = 0;
        event_scope = [];
        axioms = [];
        type_configs = [];
        violation = "";
      }
  in
  let () =
    List.iter
      (function
        | StepBound i -> setting := { !setting with step_bound = i }
        | EventScope i -> setting := { !setting with event_scope = i }
        | Axioms i -> setting := { !setting with axioms = i }
        | TypeConfigs i -> setting := { !setting with type_configs = i }
        | Violation i -> setting := { !setting with violation = i })
      fields
  in
  MClient !setting

let default_serv_field = "dest" #: (Nt.Ty_constructor ("server", []))

let add_server_field_record_type = function
  | Nt.Ty_record l -> Nt.Ty_record (default_serv_field :: l)
  | _ -> Sugar._die [%here]

let remove_server_field_record_type = function
  | Nt.Ty_record l ->
      Nt.Ty_record
        (List.filter (fun x -> not (String.equal x.x default_serv_field.x)) l)
  | _ -> Sugar._die [%here]

type spec_tyctx = {
  p_tyctx : Nt.nt Typectx.ctx;
  reqresp_ctx : string Typectx.ctx;
  wrapper_ctx : ((Nt.nt, string) typed * (Nt.nt, string) typed) Typectx.ctx;
  abstract_tyctx : concrete_type Typectx.ctx;
  event_tyctx : (Nt.nt, string) typed list Typectx.ctx;
  event_kindctx : event_kind Typectx.ctx;
  regex_tyctx : Nt.nt Typectx.ctx;
  tyctx : Nt.nt Typectx.ctx;
  field_assignment : string Typectx.ctx;
}

let init_spec_tyctx =
  {
    p_tyctx = Typectx.emp;
    reqresp_ctx = Typectx.emp;
    wrapper_ctx = Typectx.emp;
    abstract_tyctx = Typectx.emp;
    event_tyctx = Typectx.emp;
    event_kindctx = Typectx.emp;
    regex_tyctx = Typectx.emp;
    tyctx = Typectx.emp;
    field_assignment = Typectx.emp;
  }

let mk_regex_func_type args =
  let argsty =
    List.map
      (fun x ->
        match x.ty with Nt.Ty_unknown -> Sugar._die [%here] | nt -> nt)
      args
  in
  Nt.construct_arr_tp (argsty, mk_p_regex_ty)

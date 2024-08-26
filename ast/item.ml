open Sexplib.Std
open Mtyped
open Prop
open Sevent
open Regex
open Constructor_declaration
open Common

type event_kind = Req | Resp | Hidden [@@deriving sexp]

type concrete_type =
  | CBaseType of { superty : Nt.t; use_config : bool }
  | CEnumType of { enum_name : string; enum_elems : string list }
    (* enum type *)
[@@deriving sexp]

let concrete_type_to_nt = function
  | CBaseType { superty; _ } -> superty
  | CEnumType { enum_name; _ } -> mk_p_abstract_ty enum_name

type client_field =
  | StepBound of int
  | EventScope of string list
  | Axioms of string list
  | TypeConfigs of string list
  | Violation of string
[@@deriving sexp]

type client_setting = {
  client_name : string;
  step_bound : int;
  event_scope : string list;
  axioms : string list;
  type_configs : string list;
  violation : string;
}
[@@deriving sexp]

type 't item =
  | MFieldAssign of { field : string; assignment : string }
  | MValDecl of (Nt.t, string) typed
  | MAbstractType of (concrete_type, string) typed
  | MEventDecl of { ev : (Nt.t, string) typed; event_kind : event_kind }
  | MRegex of { name : (Nt.t, string) typed; automata : ('t, 't sevent) regex }
  | MClient of client_setting
[@@deriving sexp]

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
  | Nt.Ty_record l ->
      Nt.Ty_record ((default_serv_field.x, default_serv_field.ty) :: l)
  | _ -> Sugar._die [%here]

let remove_server_field_record_type = function
  | Nt.Ty_record l ->
      Nt.Ty_record
        (List.filter
           (fun (x, _) -> not (String.equal x default_serv_field.x))
           l)
  | _ -> Sugar._die [%here]

type spec_tyctx = {
  reqresp_ctx : string Typectx.ctx;
  wrapper_ctx : ((Nt.t, string) typed * (Nt.t, string) typed) Typectx.ctx;
  abstract_tyctx : concrete_type Typectx.ctx;
  event_tyctx : (string * Nt.t) list Typectx.ctx;
  event_kindctx : event_kind Typectx.ctx;
  regex_tyctx : Nt.t Typectx.ctx;
  tyctx : Nt.t Typectx.ctx;
  field_assignment : string Typectx.ctx;
}

let init_spec_tyctx =
  {
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
      (fun x -> match x.ty with Some nt -> nt | None -> Sugar._die [%here])
      args
  in
  Nt.construct_arr_tp (argsty, mk_p_regex_ty)

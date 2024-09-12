open Sexplib.Std
open Zutils
open Common
open AutomataLibrary

(** constant has types independent from type context *)
type p_const =
  | PUnit
  | PBool of bool
  | PInt of int
  | PDefault of Nt.nt
  (* | PSeqLit of p_const list *)
  (* | PRecordLit of (string * p_const) list *)
  | PStr of string
  | PHalt
  | PError
  | PRandomBool
[@@deriving sexp, show, eq, ord]

let p_infix_operator =
  [ "&&"; "||"; "-"; "+"; "=="; "!="; ">"; "<"; ">="; "<="; "*"; "\\"; "in" ]

(** Also p statement *)
type 't p_expr =
  | PThis
  | PNull
  | Pid of (('t, string) typed[@free])
  | PConst of p_const
  | PApp of {
      pfunc : (('t, string) typed[@free]);
      args : ('t, 't p_expr) typed list;
    }
  | PAccess of {
      container : ('t, 't p_expr) typed;
      index : ('t, 't p_expr) typed;
    }
  | PRecord of (string * ('t, 't p_expr) typed) list
  | PField of { record : ('t, 't p_expr) typed; field : string }
  | PAssign of {
      lvalue : ('t, 't p_expr) typed;
      rvalue : ('t, 't p_expr) typed;
    }
  | PDeref of ('t, 't p_expr) typed
  | PLet of {
      lhs : (('t, string) typed[@free]);
      rhs : ('t, 't p_expr) typed;
      body : ('t, 't p_expr) typed;
    }
  | PSeq of { rhs : ('t, 't p_expr) typed; body : ('t, 't p_expr) typed }
  | ForeachSet of {
      elem : ('t, string) typed;
      set : ('t, 't p_expr) typed;
      body : ('t, 't p_expr) typed;
    }
  | ForeachMap of {
      key : ('t, string) typed;
      map : ('t, 't p_expr) typed;
      body : ('t, 't p_expr) typed;
    }
  | PIf of {
      condition : ('t, 't p_expr) typed;
      tbranch : ('t, 't p_expr) typed;
      fbranch : ('t, 't p_expr) typed option;
    }
  | PSend of {
      dest : ('t, 't p_expr) typed;
      event_name : string;
      payload : ('t, 't p_expr) typed;
    }
  | PGoto of string
  | PBreak
  | PReturn of ('t, 't p_expr) typed
  | PPrintf of (string * ('t, 't p_expr) typed list)
[@@deriving sexp, show, eq, ord]

let layout_sexp_p_expr pexpr =
  sexp_of_p_expr (fun _ -> Sexplib.Sexp.unit) pexpr |> Sexplib.Sexp.to_string

(** P Compiled File Convention  *)
let p_response_actions_domain =
  "response_actions" #: (mk_p_set_ty mk_p_string_ty)

let lib_set_is_empty = "set_is_empty" #: Nt.Ty_bool
let lib_intersection_set = "intersection_set" #: (mk_p_set_ty mk_p_string_ty)
let lib_set_union = "int_set_union" #: (mk_p_set_ty Nt.Ty_int)
let server_domain_decl = "server_domain" #: (mk_p_seq_ty mk_p_machine_ty)

(* let machine_local_server_decl = "local_server" #: mk_p_machine_ty *)
let qtype_init_function_decl = "qtype_init" #: Nt.Ty_unit
let state_decl = "state" #: Nt.Ty_int
let gprop_id_decl = "gprop_id" #: Nt.Ty_int
let default_world_name = "world"
let default_tmp_world_name = "tmp_world"
let world_to_gprop_id_function_decl = "world_to_gprop_id" #: Nt.Ty_int
let action_name_mapping = "action_name"
let validate_function_decl op = (spf "validate_%s" op.x) #: Nt.Ty_bool
let source_field_decl = "source" #: (mk_p_abstract_ty "machine")
let next_world_function op = spf "next_world_%s" op
let next_world_function_decl op = (next_world_function op.x) #: Nt.Ty_unit
let action_domain_declar = "action_domain" #: (mk_p_set_ty mk_p_string_ty)
let action_domain_init_function_decl = "action_domain_init" #: Nt.Ty_unit
let get_available_actions_function_name = "get_available_actions"
let global_event_name = "_global_"

let get_available_actions_function_decl =
  get_available_actions_function_name #: (mk_p_set_ty mk_p_string_ty)

let random_event_function_name op = spf "random_event_%s" op

let random_event_function_decl op =
  (random_event_function_name op.x) #: (Nt.mk_arr Nt.Ty_unit op.ty)

let input_name = "input"
let check_final_function_name = "check_final"
let check_final_function_decl = check_final_function_name #: Nt.Ty_bool
let loop_state_name = "Loop"
let init_state_name = "Init"
let error_state_name = "Error"
let instantiate_action_function_name op = spf "instantiate_action_%s" op.x

let realize_instantiated_action_function op =
  (spf "realize_instantiated_action_%s" op.x) #: Nt.Ty_unit

let action_name_mapping_decl =
  action_name_mapping #: (mk_p_map_ty Ty_int mk_p_string_ty)

(* the type of SFA's transitions *)
let raw_transition_type =
  mk_p_map_ty Nt.Ty_int (* the state *)
    (mk_p_map_ty mk_p_string_ty (* the event name *)
       (mk_p_map_ty Nt.Ty_int (* the prop index *)
          Nt.Ty_int (* the next state *)))

let lib_seq_string_to_set = "seq_string_to_set" #: (mk_p_set_ty mk_p_string_ty)

(** P AST Builder  *)

let mk_p_self = PThis #: mk_p_machine_ty
let mk_p_printf format es = (PPrintf (format, es)) #: Nt.Ty_unit
let mk_p_break = PBreak #: Nt.Ty_unit
let mk_p_default nt = (PConst (PDefault nt)) #: nt
let mk_pid id = (Pid id) #: id.ty
let mk_p_this = PThis #: Nt.Ty_unit

let mk_p_ite condition tbranch fbranch =
  (PIf { condition; tbranch; fbranch }) #: Nt.Ty_unit

let mk_p_it condition tbranch =
  (PIf { condition; tbranch; fbranch = None }) #: Nt.Ty_unit

let mk_field record field =
  match record.ty with
  | Nt.Ty_record l -> (
      match List.find_opt (fun x -> String.equal x.x field) l with
      | None -> _die [%here]
      | Some x -> (PField { record; field }) #: x.ty)
  | _ ->
      _die_with [%here]
        (spf "%s.%s has not a record type: %s"
           (layout_sexp_p_expr record.x)
           field (Nt.layout record.ty))

let mk_p_send dest event_name payload =
  (PSend { dest; event_name; payload }) #: Nt.Ty_unit

(** TODO: record type and tuple type...*)
let mk_depair (record : (Nt.nt, Nt.nt p_expr) typed) =
  match record.ty with
  | Nt.Ty_tuple [ t1; t2 ] ->
      let fst = (PField { record; field = "0" }) #: t1 in
      let snd = (PField { record; field = "1" }) #: t2 in
      (fst, snd)
  | Nt.Ty_record [ x1; x2 ] ->
      let fst = (PField { record; field = "0" }) #: x1.ty in
      let snd = (PField { record; field = "1" }) #: x2.ty in
      (fst, snd)
  | _ -> _die_with [%here] (spf "die: %s" (Nt.layout record.ty))

let mk_field_nth record n =
  match record.ty with
  | Nt.Ty_record l -> (
      match List.nth_opt l n with
      | None -> _die [%here]
      | Some { x = field; ty } -> (PField { record; field }) #: ty)
  | _ -> _die [%here]

let mk_p_app pfunc args =
  let _, retty = Nt.destruct_arr_tp pfunc.ty in
  (PApp { pfunc; args }) #: retty

let mk_p_add_set e1 e2 =
  match e1.ty with
  | Nt.Ty_constructor ("set", [ t1 ]) ->
      if Nt.equal_nt t1 e2.ty then
        let f =
          "add_set" #: (Nt.construct_arr_tp ([ e1.ty; e2.ty ], Nt.Ty_unit))
        in
        mk_p_app f [ e1; e2 ]
      else
        _die_with [%here]
          (spf "expect type %s but get type %s" (Nt.layout t1) (Nt.layout e2.ty))
  | _ -> _die [%here]

let mk_p_map_keys e1 =
  match e1.ty with
  | Nt.Ty_constructor ("map", [ t1; _ ]) ->
      let f = "keys" #: (Nt.mk_arr e1.ty (mk_p_set_ty t1)) in
      mk_p_app f [ e1 ]
  | _ -> _die [%here]

let mk_p_map_values e1 =
  match e1.ty with
  | Nt.Ty_constructor ("map", [ _; t2 ]) ->
      let f = "values" #: (Nt.mk_arr e1.ty (mk_p_set_ty t2)) in
      mk_p_app f [ e1 ]
  | _ -> _die [%here]

let mk_set_intersection e1 e2 =
  match e1.ty with
  | Nt.Ty_constructor ("set", [ t2 ]) when Nt.equal_nt e1.ty e2.ty ->
      let f =
        "intersection" #: (Nt.construct_arr_tp ([ e1.ty; e1.ty ], e1.ty))
      in
      mk_p_app f [ e1; e2 ]
  | _ -> _die [%here]

let mk_p_choose pexpr =
  match pexpr.ty with
  | Nt.Ty_constructor (name, [ nt ])
    when String.equal name "set" || String.equal name "seq" ->
      let pfunc = "choose" #: (Nt.mk_arr pexpr.ty nt) in
      mk_p_app pfunc [ pexpr ]
  | Nt.Ty_int ->
      let pfunc = "choose" #: (Nt.mk_arr Nt.Ty_int Nt.Ty_int) in
      mk_p_app pfunc [ pexpr ]
  | _ -> _die [%here]

open Zdatatype

let mk_p_seq rhs body = (PSeq { rhs; body }) #: body.ty
let mk_p_seqs es e = List.fold_right mk_p_seq es e
let ( <++> ) = mk_p_seq

let mk_p_seqs_ es =
  match List.last_destruct_opt es with
  | None -> _die [%here]
  | Some (es, e) -> mk_p_seqs es e

let mk_p_assign (lvalue, rvalue) = (PAssign { lvalue; rvalue }) #: Nt.Ty_unit

let mk_p_vassign (lvalue, rvalue) =
  (PAssign { lvalue = mk_pid lvalue; rvalue }) #: Nt.Ty_unit

let mk_p_let lhs rhs body = (PLet { lhs; rhs; body }) #: body.ty
let mk_return_void = (PReturn (PConst PUnit) #: Nt.Ty_unit) #: Nt.Ty_unit
let mk_p_int i = (PConst (PInt i)) #: Nt.Ty_int
let mk_p_bool b = (PConst (PBool b)) #: Nt.Ty_bool
let mk_p_string str = (PConst (PStr str)) #: (mk_p_abstract_ty "string")
let mk_random_bool = (PConst PRandomBool) #: Nt.Ty_bool

let mk_random_int =
  mk_p_app "choose" #: (Nt.mk_arr Nt.Ty_int Nt.Ty_int) [ mk_p_int 10000 ]

let mk_random_from_seq seq =
  match seq.ty with
  | Nt.Ty_constructor ("set", [ t2 ]) ->
      mk_p_app "choose" #: (Nt.mk_arr seq.ty t2) [ seq ]
  | _ -> _die_with [%here] (Nt.layout seq.ty)

let mk_random_from_enum l =
  mk_p_app
    "choose" #: (Nt.mk_arr Nt.Ty_int Nt.Ty_int)
    [ mk_p_int (List.length l) ]

let mk_p_access (container, index) =
  let e = PAccess { container; index } in
  let t2 =
    match container.ty with
    | Nt.Ty_constructor ("map", [ t1; t2 ]) ->
        if Nt.equal_nt t1 index.ty then t2
        else
          _die_with [%here] (spf "%s != %s" (Nt.layout t1) (Nt.layout index.ty))
    | Nt.Ty_constructor ("set", [ t2 ]) ->
        if Nt.equal_nt Nt.Ty_int index.ty then t2
        else
          _die_with [%here]
            (spf "%s != %s" (Nt.layout Nt.Ty_int) (Nt.layout index.ty))
    | Nt.Ty_constructor ("seq", [ t2 ]) ->
        (* HACK: server type = int *)
        if
          Nt.equal_nt Nt.Ty_int index.ty
          || Nt.equal_nt (mk_p_abstract_ty "server") index.ty
        then t2
        else
          _die_with [%here]
            (spf "%s != %s" (Nt.layout Nt.Ty_int) (Nt.layout index.ty))
    | _ ->
        _die_with [%here]
          (spf "%s[%s]?" (Nt.layout container.ty) (Nt.layout index.ty))
  in
  e #: t2

let mk_p_vaccess (container, index) = mk_p_access (mk_pid container, index)

let mk_foreach_map_with_key key map body =
  let value = mk_p_access (map, mk_pid key) in
  (ForeachMap { key; map; body = body value }) #: Nt.Ty_unit

let mk_foreach_map map body =
  match map.ty with
  | Nt.Ty_constructor ("map", [ t1; t2 ]) ->
      let key = (Rename.unique "key") #: t1 in
      mk_foreach_map_with_key key map (body key)
  | _ -> _die [%here]

let mk_foreach_set set body =
  match set.ty with
  | Nt.Ty_constructor ("set", [ t ]) ->
      let elem = (Rename.unique "elem") #: t in
      (ForeachSet { elem; set; body = body (mk_pid elem) }) #: Nt.Ty_unit
  | _ -> _die [%here]

let mk_p_record l =
  let tys = List.map (fun (name, e) -> name #: e.ty) l in
  let ty = mk_p_record_ty tys in
  (PRecord l) #: ty

let mk_p_tuple l = mk_p_record @@ List.mapi (fun i e -> (string_of_int i, e)) l

let mk_return x =
  let rec aux x =
    match x.x with
    | PGoto _ -> x
    | PSeq { rhs; body } -> (PSeq { rhs; body = aux body }) #: x.ty
    | PLet { lhs; rhs; body } -> (PLet { lhs; rhs; body = aux body }) #: x.ty
    | _ -> (PReturn x) #: x.ty
  in
  aux x

let mk_p_halt = mk_return @@ ((PConst PHalt) #: Nt.Ty_unit)

let mk_p_eq e1 e2 =
  if Nt.equal_nt e1.ty e2.ty then
    mk_p_app
      "==" #: (Nt.construct_arr_tp ([ e1.ty; e1.ty ], Nt.Ty_bool))
      [ e1; e2 ]
  else _die [%here]

let mk_p_in e1 e2 =
  mk_p_app "in" #: (Nt.construct_arr_tp ([ e1.ty; e2.ty ], Ty_bool)) [ e1; e2 ]

let mk_p_error = mk_return @@ ((PConst PError) #: Nt.Ty_unit)
let mk_p_goto name = (PGoto name) #: Nt.Ty_unit

let mk_p_or e1 e2 =
  mk_p_app
    "||" #: (Nt.construct_arr_tp ([ Nt.Ty_bool; Nt.Ty_bool ], Nt.Ty_bool))
    [ e1; e2 ]

let mk_p_not a = mk_p_app "!" #: (Nt.mk_arr Nt.Ty_bool Nt.Ty_bool) [ a ]

let mk_p_ors l =
  match l with
  | [] -> mk_p_bool false
  | [ e ] -> e
  | e :: es -> List.fold_left mk_p_or e es

type pexpr = (Nt.nt, Nt.nt p_expr) typed

let init_p_int_map (m : (pexpr -> pexpr) IntMap.t) (expr : pexpr) =
  (* let () = *)
  (*   Printf.printf "%s: %s\n" (layout_p_expr 0 expr.x) (layout_pnt expr.ty) *)
  (* in *)
  let e1 = mk_p_assign (expr, mk_p_default expr.ty) in
  let es =
    IntMap.fold
      (fun i f res ->
        let lvalue = mk_p_access (expr, mk_p_int i) in
        f lvalue :: res)
      m []
  in
  match List.last_destruct_opt es with
  | None -> _die [%here]
  | Some (es, e') -> mk_p_seqs (e1 :: es) e'

let init_p_int64_map (m : (pexpr -> pexpr) StateMap.t) (expr : pexpr) =
  let e1 = mk_p_assign (expr, mk_p_default expr.ty) in
  let es =
    StateMap.fold
      (fun i f res ->
        let lvalue = mk_p_access (expr, mk_p_int i) in
        f lvalue :: res)
      m []
  in
  match List.last_destruct_opt es with
  | None -> _die [%here]
  | Some (es, e') -> mk_p_seqs (e1 :: es) e'

let init_p_str_map (m : (pexpr -> pexpr) StrMap.t) (expr : pexpr) =
  let e1 = mk_p_assign (expr, mk_p_default expr.ty) in
  let es =
    StrMap.fold
      (fun i f res ->
        let lvalue = mk_p_access (expr, mk_p_string i) in
        f lvalue :: res)
      m []
  in
  match List.last_destruct_opt es with
  | None -> _die [%here]
  | Some (es, e') -> mk_p_seqs (e1 :: es) e'

type 't p_func = {
  params : ('t, string) typed list;
  local_vars : ('t, string) typed list;
  body : ('t, 't p_expr) typed;
}
[@@deriving sexp, show, eq, ord]

type state_label = Hot | Cold | Start [@@deriving sexp, show, eq, ord]

type func_label = Plain | Entry | Exit | Listen of string
[@@deriving sexp, show, eq, ord]

type 't p_state = {
  name : string;
  state_label : state_label list;
  state_body : (('t, func_label) typed * 't p_func) list;
}
[@@deriving sexp, show, eq, ord]

type 't p_machine_decl = {
  name : string;
  local_vars : ('t, string) typed list;
  local_funcs : (('t, string) typed * 't p_func) list;
  states : 't p_state list;
}
[@@deriving sexp, show, eq, ord]

type 't p_item =
  | PEnumDecl of (string * string list)
  | PMachine of 't p_machine_decl
  | PTypeDecl of (Nt.nt, string) typed
  | PEventDecl of (Nt.nt, string) typed
  | PGlobalFunc of ('t, string) typed * 't p_func
  | PPrimFuncDecl of ('t, string) typed
[@@deriving sexp, show, eq, ord]

let p_expr_to_str expr =
  Sexplib.Sexp.to_string @@ sexp_of_p_expr (fun _ -> Sexplib.Sexp.unit) expr

let map_on_p_machine f items =
  List.map (function PMachine m -> PMachine (f m) | _ as item -> item) items

let mk_p_sizeof expr =
  let f = "sizeof" #: Nt.Ty_int in
  match expr.ty with
  | Nt.Ty_constructor (name, _)
    when List.exists (String.equal name) [ "set"; "seq"; "map" ] ->
      mk_p_app f [ expr ]
  | _ -> _die_with [%here] (Nt.layout expr.ty)

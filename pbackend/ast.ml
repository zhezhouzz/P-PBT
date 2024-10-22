open Sexplib.Std
open Zutils

(* open Common *)
(* open AutomataLibrary *)

(** constant has types independent from type context *)
type p_const =
  | PUnit
  | PBool of bool
  | PInt of int
  | PDefault of Nt.nt
  | PStr of string
  | PEnum of string
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
  | PAssert of ('t, 't p_expr) typed
  | PApp of {
      pfunc : (('t, string) typed[@free]);
      args : ('t, 't p_expr) typed list;
    }
  | PWhile of { body : ('t, 't p_expr) typed }
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
  | PRecieve of {
      event_name : string;
      input : ('t, string) typed;
      body : ('t, 't p_expr) typed;
    }
  | PGoto of string
  | PBreak
  | PReturn of ('t, 't p_expr) typed
  | PPrintf of (string * ('t, 't p_expr) typed list)
[@@deriving sexp, show, eq, ord]

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

let layout_sexp_p_expr pexpr =
  sexp_of_p_expr (fun _ -> Sexplib.Sexp.unit) pexpr |> Sexplib.Sexp.to_string

open Language
open Zdatatype

module NtMap = Map.Make (struct
  type t = Nt.nt

  let compare = Nt.compare_nt
end)

type penv = {
  gen_ctx : bool ctx;
  recvable_ctx : bool ctx;
  event_tyctx : (Nt.nt, string) typed list StrMap.t;
  (* component_table : (string * string) StrMap.t; *)
  p_tyctx : Nt.nt StrMap.t;
      (* sampling_space : (Nt.nt, Nt.nt p_expr) typed NtMap.t; *)
}

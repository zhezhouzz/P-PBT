open Sexplib.Std

type constant =
  | U
  | B of bool
  | I of int
  | Tu of constant list
  | Dt of string * constant list
  | SetLiteral of constant list
[@@deriving sexp]

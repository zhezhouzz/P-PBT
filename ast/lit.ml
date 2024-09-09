open Sexplib.Std
open Constant
open Zutils

type 't lit =
  | AC of constant
  | AVar of (('t, string) typed[@free])
  | ATu of ('t, 't lit) typed list
  | AProj of ('t, 't lit) typed * int
  | AAppOp of ('t, string) typed * ('t, 't lit) typed list
[@@deriving sexp]

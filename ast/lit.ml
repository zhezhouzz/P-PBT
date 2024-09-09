open Sexplib.Std
open Constant
open Zutils

type 't lit =
  | AC of constant
  | AVar of (('t, string) typed[@free])
  | ATu of ('t, 't lit) typed list
  | AProj of ('t, 't lit) typed * int
  | AAppOp of ('t, string) typed * ('t, 't lit) typed list
[@@deriving sexp, show, eq, ord]

let eq_lit p1 p2 = equal_lit (fun _ _ -> true) p1 p2

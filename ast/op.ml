open Sexplib.Std

type op = PrimOp of string | DtConstructor of string [@@deriving sexp]

(* a string:
   1. is in builtin_primop, then is a builtin operator.
   2. is in not builtin_primop, and with a non-lowercase alphabeta first char, then is a data constructor (include [])
   3. else, invalid
*)

let builtin_primop =
  [ "+"; "-"; "*"; "/"; ">"; ">="; "<"; "<="; "=="; "!="; "&&"; "||" ]

let eq_op = "=="
let is_builtin_op str = List.exists (String.equal str) builtin_primop

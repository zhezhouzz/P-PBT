open Zutils
open Sexplib.Std

type constructor_declaration = { constr_name : string; argsty : Nt.nt list }
[@@deriving sexp, show, eq, ord]

open Sexplib.Std
open Prop

type 't label = { ty : Nt.t; prop : 't prop } [@@deriving sexp, show, eq, ord]

let layout { ty; prop } = Printf.sprintf "<v:%s | %s>"

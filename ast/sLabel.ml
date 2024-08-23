open Sexplib.Std
open Prop

type 't label = { ty : Nt.t; prop : 't prop } [@@deriving sexp]

let layout { ty; prop } = Printf.sprintf "<v:%s | %s>"

open Sexplib.Std

type label = string [@@deriving sexp, show, eq, ord]

let layout_label (x : label) = x

open Sexplib.Std

type label = string [@@deriving sexp]

let layout_label (x : label) = x

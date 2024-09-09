open Sexplib.Std
open Zdatatype

type mt = { op : string; global_embedding : int; local_embedding : int }
[@@deriving sexp, show, eq, ord]

type mts = int list StrMap.t IntMap.t

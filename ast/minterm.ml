open Sexplib.Std
open Zzdatatype.Datatype

type mt = { op : string; global_embedding : int; local_embedding : int }
[@@deriving sexp]

type mts = int list StrMap.t IntMap.t

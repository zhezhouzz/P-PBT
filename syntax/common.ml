module type AST = sig
  type 'a ast [@@deriving sexp]

  val fv : 'a ast -> string
  val subst : 'a ast -> string -> 'a ast -> 'a ast
  val subst_id : 'a ast -> string -> string -> 'a ast
end

open Ast
open Zzdatatype.Datatype

let layout_states f s =
  List.split_by_comma f @@ List.of_seq @@ StateSet.to_seq s

let layout_qv x = spf "(%s: %s)" x.x (Nt.layout x.ty)
let layout_qvs = List.split_by " " layout_qv

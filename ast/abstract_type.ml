open Sexplib.Std
open Constant

type abstract_type_binding =
  | ATSuper of Normalty.Ntyped.t
  | ATAssigned of (Normalty.Ntyped.t * constant list)
  | ATEnum of string list
[@@deriving sexp]

let mk_super_abstract_type nt = ATSuper nt
let mk_enum_abstract_type n = ATEnum n

let _force_abstact_super_ty file line = function
  | ATSuper nt -> nt
  | _ -> Sugar._failatwith file line "die"

let _force_abstact_super_ty_opt file line = function
  | Some nt -> Some (_force_abstact_super_ty file line nt)
  | _ -> Sugar._failatwith file line "die"

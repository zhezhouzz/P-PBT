open Ast

let compare_op a b = Sexplib.Sexp.compare (sexp_of_op a) (sexp_of_op b)
let equal_op a b = Sexplib.Sexp.equal (sexp_of_op a) (sexp_of_op b)
let compare_equal a b = Sexplib.Sexp.compare (sexp_of_op a) (sexp_of_op b)

(* NOTE: there are several constructors cannot be parsed directly from the external files *)
let dt_name_for_typectx = function
  | "()" -> "TT"
  | "::" -> "Cons"
  | "[]" -> "Nil"
  | _ as s -> s

let op_name_for_typectx = function
  | PrimOp name -> name
  | DtConstructor name -> dt_name_for_typectx name

let is_dt_op str =
  let fst_char = String.get str 0 in
  Char.uppercase_ascii fst_char == fst_char

let id_eq_op = function PrimOp "==" -> true | _ -> false
let id_is_dt name = String.(equal name @@ capitalize_ascii name)
let mk_eq_op = PrimOp eq_op
let typed_op_string ty = eq_op #: Nt.(mk_arr ty (mk_arr ty bool_ty))

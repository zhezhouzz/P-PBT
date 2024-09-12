include Common
(* include Regex *)

(* include Nfa *)
(* include FiniteAutomata *)
include Minterm
include Constructor_declaration
include Item
include Inst
include Zutils
include Typectx
include Pmachine
include Wrapper

(* include Abstract_type *)
include Myconfig

let ty_set (t : Nt.t) = Nt.Ty_constructor ("set", [ t ])

module type AST = sig
  type 'a ast [@@deriving sexp, show, eq, ord]

  val fv : 'a ast -> string
  val subst : 'a ast -> string -> 'a ast -> 'a ast
  val subst_id : 'a ast -> string -> string -> 'a ast
end

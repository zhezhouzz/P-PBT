include Common
include Op
include Constant
include Lit
include Prop
include Sevent
include Regex

(* include Nfa *)
include FiniteAutomata
include Typectx
include Minterm
include Constructor_declaration
include Item
include Inst
include Mtyped
include Sugar
include Pmachine

(* include Abstract_type *)
include Myconfig

let ty_set (t : Nt.t) = Nt.Ty_constructor ("set", [ t ])

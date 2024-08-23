open Ast

type 'a loced = { y : 'a; loc : Lexing.position }
type term = Ntopt.t p_item loced list

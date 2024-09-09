open Ast

type 'a loced = { y : 'a; loc : Lexing.position }
type term = Nt.t item loced list

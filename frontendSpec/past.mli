open Ast

type 'a loced = { y : 'a; loc : Lexing.position }
type term = Nt.t option item loced list

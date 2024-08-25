open Ast

type 'a loced = { y : 'a; loc : Lexing.position }
type term = p_wrapper loced list

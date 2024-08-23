open Syntax

type 'a loced = { y : 'a; loc : Lexing.position }
type term = CharAutomata.raw_regex loced

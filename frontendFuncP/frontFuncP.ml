open Past
open Ast
open Zzdatatype.Datatype

let layout_position (p : Lexing.position) =
  let open Lexing in
  spf "At line %i, offset %i: syntax error" p.pos_lnum (p.pos_cnum - p.pos_bol)

let parse_ linebuf =
  try Parser.prog_eof Lexer.next_token linebuf with
  | Lexer.LexError msg -> raise @@ failwith (Printf.sprintf "%s%!" msg)
  | Parser.Error ->
      raise @@ failwith (layout_position @@ Lexing.lexeme_end_p linebuf)

let parse filename : Ntopt.t p_item list =
  let oc = open_in filename in
  let linebuf = Lexing.from_channel oc in
  let res = parse_ linebuf in
  close_in oc;
  List.map (fun x -> x.y) res

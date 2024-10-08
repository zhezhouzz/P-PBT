    {
      open Parser

      exception LexError of string

      let[@inline] failwith msg = raise (LexError msg)

      let[@inline] illegal c =
        failwith (Printf.sprintf "[lexer] unexpected character: '%c'(%i)" c (Char.code c))

      open Lexing
      let next_line lexbuf =
        let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <-
          { pos with pos_bol = lexbuf.lex_curr_pos;
                     pos_lnum = pos.pos_lnum + 1
          }
    }

(* regular expressions *)
let whitespace = ' ' | '\t'
let newline = "\r\n" | '\r' | '\n'
let lowercase = ['a'-'z' '_']
let uppercase = ['A'-'Z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9' '!']

let ident = (lowercase | uppercase) identchar*
let number = ['0'-'9'] ['0'-'9' '_']*


rule next_token = parse
  | eof { EOF }
  | whitespace+
    { next_token lexbuf }
  | newline
      { next_line lexbuf; next_token lexbuf }
  | "(*"
      { comment 0 lexbuf; next_token lexbuf }
  | "/*"
      { comment 0 lexbuf; next_token lexbuf }

  | "//" {one_line_comment lexbuf; next_token lexbuf }

  (* YOUR TOKENS HERE... *)
  (* keywords... *)
  | "fun" {FUN}
  | "spec" {SPEC}
  | "event" {EVENT}
  | "type" {TYPE}
  | "=" {ASSIGN}
  | "in" {IN}
  | "enum" {ENUM}
  | "machine" {MACHINE}
  | "module" {MODULE}
  | "test" {TEST}
  | "REQ" {REQ}
  | "RSP" {RSP}
  | "HIDDEN" {HIDDEN}
  | "REQRSP" {REQRESP}
  (* arithmetic operators *)
  | "-" {MINUS}
  | "+" {PLUS}
  | "==" {EQ}
  | "!=" {NEQ}
  | "<" {LT}
  | ">" {GT}
  | "<=" {LE}
  | ">=" {GE}
  | "*" {STAR}
  | '%' {MOD}
  | '/' {DIV}
  (* logic operators *)
  | "$" {RANDOMBOOL}
  | "$?" {RANDOMBOOLQ}
  | "!" {NOT}
  | "&&" {AND}
  | "||" {OR}
  | "true" {TRUE}
  | "false" {FALSE}
  (* splitter *)
  | "." {DOT}
  | "," {COMMA}
  | ":" {COLON}
  | ";" {SEMICOLON}
  (* paranthesis *)
  | '(' { LPAR }
  | ')' { RPAR }
  | "[" {LSEQPRAN}
  | "]" {RSEQPRAN}
  | "{" {LBRACKET}
  | "}" {RBRACKET}
  (* type *)
  | "int" {INT}
  | "bool" {BOOL}
  (* lex identifiers last, so keywords are not lexed as identifiers *)
  | number as number { NUMBER (int_of_string number) }
  | ident as ident { IDENT ident }
  | '"' {read_string (Buffer.create 10) lexbuf}
  (* no match? raise exception *)
  | _ as c { if Char.code c > 160 then next_token lexbuf else illegal c }
and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (Failure ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (Failure ("String is not terminated")) }


(* allow nested comments, like OCaml *)
and comment nesting = parse
  | "(*"
    { comment (nesting+1) lexbuf }
  | "/*"
      { comment (nesting+1) lexbuf }
  | "*)"
    { if nesting > 0 then comment (nesting - 1) lexbuf }
  | "*/"
      { if nesting > 0 then comment (nesting - 1) lexbuf }
  | eof
    { failwith "[lexer] unterminated comment at EOF" }
  | _
    { comment nesting lexbuf }

and one_line_comment = parse
  | eof { () }
  | newline { next_line lexbuf }
  | _ { one_line_comment lexbuf }

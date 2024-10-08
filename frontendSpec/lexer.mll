    {
      open Parser

      exception LexError of string

      let[@inline] failwith msg = raise (LexError msg)

      let[@inline] illegal c =
        failwith (Printf.sprintf "[lexer] unexpected character: '%c'" c)

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

  (* YOUR TOKENS HERE... *)
  (* keywords... *)
  | "func" {FUNC}
  | "match" {MATCH}
  | "event" {EVENT}
  | "type" {TYPE}
  | "const" {CONST}
  | "spec" {SPEC}
  | "lit" {LITDECL}
  | "=" {ASSIGN}
  | "let" {LET}
  | "in" {IN}
  | "all" {ALL}
  | "request" {REQUEST}
  | "response" {RESPONSE}
  | "enum" {ENUM}
  | "hidden" {HIDDEN}
  | "generator" {GENERATOR}
  | "scope" {SCOPE}
  | "axiom" {AXIOM}
  | "config" {CONFIG}
  | "violation" {VIOLATION}
  | "step" {STEP}
  | "atom" {ATOM}
  | "regex" {REGEX}
  | "//" {PCOMMENT}
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
  | '\\' {DIV}
  (* logic operators *)
  | "not" {NOT}
  | "&&" {AND}
  | "||" {OR}
  | "==>" {IMPL}
  | "<==>" {IFF}
  | "forall" {FORALL}
  | "exists" {EXISTS}
  | "pi" {PI}
  | "true" {TRUE}
  | "false" {FALSE}
  (* splitter *)
  | "." {DOT}
  | "," {COMMA}
  | ":" {COLON}
  | "::" {CCOLON}
  | ";" {SEMICOLON}
  | "->" {ARROW}
  | "|" {BAR}
  (* paranthesis *)
  | '(' { LPAR }
  | ')' { RPAR }
  | "<[" {LEPAR}
  | "]>" {REPAR}
  | "[" {LSEQPRAN}
  | "]" {RSEQPRAN}
  | "{" {LBRACKET}
  | "}" {RBRACKET}
  (* regex *)
  | "emp" {EMP}
  | "eps" {EPSILON}
  | "ctx" {CTX}
  | "rep" {REPEAT}
  | '~' {CONCAT}
  (* type *)
  | "int" {INT}
  | "bool" {BOOL}
  | "unit" {UNIT}
  | '\'' {PRIME}
  | "<:" {SUBTYPING}
  (* dummy char *)
  | '#' {SHARP}
  (* lex identifiers last, so keywords are not lexed as identifiers *)
  | number as number { NUMBER (int_of_string number) }
  | ident as ident { IDENT ident }
  | '"' {read_string (Buffer.create 10) lexbuf}
  (* no match? raise exception *)
  | _ as c { illegal c }
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

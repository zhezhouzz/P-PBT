%{
    open Past (* open Grammar *)
    open Syntax

    let _get {y; _} = y
         %}

(* tokens *)
(* keywords *)
%token EOF TYPE ASSIGN FUN VAR EVENT IN ENUM MACHINE SPEC MODULE TEST REQ RSP HIDDEN REQRESP
(* arithmetic operators *)
%token PLUS MINUS STAR DIV LT GT LE GE NEQ EQ MOD
(* logic operators *)
%token NOT AND OR TRUE FALSE RANDOMBOOL RANDOMBOOLQ
(* splitter *)
%token COLON COMMA SEMICOLON DOT
(* paranthesis *)
%token LSEQPRAN RSEQPRAN LPAR RPAR LBRACKET RBRACKET
(* type *)
%token INT BOOL
%token <string> IDENT
%token <string> STRING
%token <int> NUMBER

(* start symbol *)
%start <Past.term> prog_eof
%on_error_reduce statement_list
%%

nt:
  | INT {Nt.Ty_int}
  | BOOL {Nt.Ty_bool}
  | id=IDENT LSEQPRAN nt=nt RSEQPRAN {Nt.Ty_constructor (id, [nt]) }
  | id=IDENT LSEQPRAN nt1=nt COMMA nt2=nt RSEQPRAN {Nt.Ty_constructor (id, [nt1; nt2]) }
  | id=IDENT {Nt.Ty_constructor (id, [])}
  | MACHINE {Nt.Ty_constructor ("machine", [])}
  | EVENT {Nt.Ty_constructor ("event", [])}
  | LPAR ts=type_feilds RPAR {Nt.Ty_record ts}
  | LPAR ts=type_tuple RPAR {Nt.Ty_tuple ts}
;

type_feilds:
  | id=IDENT COLON nt=nt {[(id #: nt)]}
  | id=IDENT COLON nt=nt COMMA ts=type_feilds {(id #: nt) :: ts}
;

type_tuple:
  | nt=nt {[nt]}
  | nt=nt COMMA ts=type_tuple {nt :: ts}
;

enum_elem_list:
  | c1=IDENT {[c1]}
  | c1=IDENT ASSIGN NUMBER {[c1]}
  | c=IDENT COMMA cs=enum_elem_list {c :: cs}
  | c=IDENT ASSIGN NUMBER COMMA cs=enum_elem_list {c :: cs}
  ;

any_without_semi:
  (* keywords *)
  | ASSIGN {()}
    | FUN {()}
    | VAR {()}
    | IN {()}
    | MACHINE {()}
    | EVENT {()}
    (* arithmetic operators *)
    | PLUS {()}
    | MINUS {()}
    | STAR {()}
    | DIV {()}
    | LT {()}
    | GT {()}
    | LE {()}
    | GE {()}
    | NEQ {()}
    | EQ {()}
    | MOD {()}
    (* logic operators *)
    | NOT {()}
    | AND {()}
    | OR {()}
    | TRUE {()}
    | FALSE {()}
    | RANDOMBOOL {()}
    | RANDOMBOOLQ {()}
    (* splitter *)
    | COLON {()}
    | COMMA {()}
    | DOT {()}
    (* paranthesis *)
    | LPAR {()}
    | RPAR {()}
    | LSEQPRAN {()}
    | RSEQPRAN {()}
    (* type *)
    | INT {()}
    | BOOL {()}
    | IDENT {()}
    | STRING {()}
    | NUMBER {()}
    | LBRACKET any* RBRACKET {()}
  ;

any:
  | any_without_semi {()}
  | SEMICOLON {()}
  | LBRACKET any* RBRACKET {()}
;

func_type_decl:
  | nt=nt {(nt, Nt.Ty_unit)}
  | nt1=nt COLON nt2=nt {(nt1, nt2)}
  | LPAR RPAR {(Nt.Ty_unit, Nt.Ty_unit)}
  | LPAR RPAR COLON nt2=nt {(Nt.Ty_unit, nt2)}

indent_or_comma:
  | IDENT {()}
  | COMMA {()}
;

spec_event:
  | REQ event_name=IDENT ASSIGN p_event_name=IDENT COLON spec_event_type=nt {{y = mk_spec_event_decl (event_name, p_event_name) spec_event_type Req; loc = $startpos}}
  | RSP event_name=IDENT ASSIGN p_event_name=IDENT COLON spec_event_type=nt {{y = mk_spec_event_decl (event_name, p_event_name) spec_event_type Resp; loc = $startpos}}
  | HIDDEN event_name=IDENT ASSIGN p_event_name=IDENT COLON spec_event_type=nt {{y = mk_spec_event_decl (event_name, p_event_name) spec_event_type Hidden; loc = $startpos}}
  | REQ event_name=IDENT ASSIGN p_event_name=IDENT {{y = mk_spec_event_decl (event_name, p_event_name) (Nt.Ty_record []) Req; loc = $startpos}}
  | RSP event_name=IDENT ASSIGN p_event_name=IDENT {{y = mk_spec_event_decl (event_name, p_event_name) (Nt.Ty_record []) Resp; loc = $startpos}}
  | HIDDEN event_name=IDENT ASSIGN p_event_name=IDENT {{y = mk_spec_event_decl (event_name, p_event_name) (Nt.Ty_record []) Hidden; loc = $startpos}}
;

statement:
  | ENUM enum_name=IDENT LBRACKET elems=enum_elem_list RBRACKET {{y = WrapperEnum {enum_name; elems}; loc = $startpos}}
  | TYPE type_name=IDENT SEMICOLON {{y = WrapperTypeAlias {type_name; alias_type = Nt.Ty_any} ; loc = $startpos}}
  | TYPE type_name=IDENT ASSIGN alias_type=nt SEMICOLON {{y = WrapperTypeAlias {type_name; alias_type} ; loc = $startpos}}
  | EVENT event_name=IDENT SEMICOLON {{y = WrapperEventDecl { event_name; event_type = Nt.Ty_record []}; loc = $startpos}}
  | EVENT event_name=IDENT COLON event_type=nt SEMICOLON {{y = WrapperEventDecl { event_name; event_type}; loc = $startpos}}
  | spec_event=spec_event SEMICOLON {spec_event}
  | MACHINE id=IDENT LBRACKET any* RBRACKET {{y = mk_machine_decl id; loc = $startpos}}
  | FUN IDENT func_type_decl LBRACKET any* RBRACKET {{y = Dummy; loc = $startpos}}
    (* FFI *)
    | FUN IDENT func_type_decl IDENT* SEMICOLON {{y = Dummy; loc = $startpos}}
    | SPEC indent_or_comma+ LBRACKET any* RBRACKET {{y = Dummy; loc = $startpos}}
    | MODULE any_without_semi* SEMICOLON {{y = Dummy; loc = $startpos}}
    | TEST any_without_semi* SEMICOLON {{y = Dummy; loc = $startpos}}
    (* SEND RECEIVE *)
    | MACHINE id=IDENT indent_or_comma+ SEMICOLON indent_or_comma+ SEMICOLON LBRACKET any* RBRACKET {{y = mk_machine_decl id; loc = $startpos}}
  | REQRESP req=IDENT resp=IDENT SEMICOLON {{y = ReqResp {req; resp}; loc = $startpos}}
  ;

statement_list:
  | c=statement cs=statement_list {c :: cs}
  | c=statement {[c]}
  ;

prog_eof:
  | s=statement_list ; EOF { s }
  | s=statement_list SEMICOLON ; EOF { s }
  | EOF { [] }
;
%%

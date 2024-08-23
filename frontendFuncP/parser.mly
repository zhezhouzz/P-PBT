%{
    open Past (* open Grammar *)
    open Syntax

    let _get {y; _} = y
    let _gets ls = List.map _get ls
         %}

(* tokens *)
(* keywords *)
%token EOF TYPEDEF CONSTDEF SPECDEF MACHINEDEF FUNCDECL EVENTDECL LITDECL LET FUNCTION ALL GOTO DEREF
%token STATE HOT COLD START PLAIN ENTRY EXIT LISTEN ON LOCAL FUNC THIS HALT NULL RANDOMBOOL
(* arithmetic operators *)
%token PLUS MINUS STAR DIV LT GT LE GE NEQ EQ
(* logic operators *)
%token NOT AND OR TRUE FALSE IMPL IFF FORALL EXISTS PI IN
(* splitter *)
%token COLON ARROW COMMA BAR SEMICOLON COLONEQ ASSIGN
(* paranthesis *)
%token LSEQPRAN RSEQPRAN LPAR RPAR LEPAR REPAR LBRACKET RBRACKET
(* regex *)
%token DOT EMP EPSILON CTX REPEAT CONCAT
(* type *)
%token INT BOOL SUBTYPING UNIT PRIME
%token <string> IDENT
%token <string> STRING
%token <int> NUMBER

(* start symbol *)
%start <Past.term> prog_eof
%on_error_reduce item_list
%%

base_nt:
  | PRIME id=IDENT {Nt.Ty_var id}
  | INT {Nt.Ty_int}
  | BOOL {Nt.Ty_bool}
  | UNIT {Nt.Ty_unit}
  | nt1=nt ARROW nt2=nt {Nt.mk_arr nt1 nt2}
  | nt=nt id=IDENT {Nt.Ty_constructor (id, [nt]) }
  | id=IDENT {Nt.Ty_constructor (id, [])}
  | LPAR nt=nt RPAR {nt}
  | LT ts=type_fields GT {Nt.Ty_record ts}
  | LT ts=type_fields SEMICOLON GT {Nt.Ty_record ts}
;

type_fields:
  | id=IDENT COLON nt=base_nt {[(id, nt)]}
  | id=IDENT COLON nt=base_nt SEMICOLON ts=type_fields {(id, nt) :: ts}
;

product_nt:
  | nt1=base_nt STAR nt2=product_nt {nt1 :: nt2}
  | nt1=base_nt STAR nt2=base_nt {[nt1; nt2]}
;

arr_nt:
  | nt1=base_nt ARROW nt2=arr_nt {Nt.mk_arr nt1 nt2}
  | nt1=base_nt ARROW nt2=base_nt {Nt.mk_arr nt1 nt2}
;

nt:
  | nt=base_nt {nt}
  | nt=arr_nt {nt}
  | nts=product_nt {Nt.mk_tuple nts}
  ;


biop:
  | PLUS {"+"}
  | MINUS {"-"}
  | STAR {"*"}
  | DIV {"/"}
  | LT {"<"}
  | GT {">"}
  | LE {"<="}
  | GE {">="}
  | EQ {"=="}
  | NEQ {"!="}
  | AND {"&&"}
  | OR {"||"}
  | IN {"in"}
;

typed_var:
  | LPAR id=IDENT COLON nt=nt RPAR {id #: (Some nt)}
  | id=IDENT {id #: None}
;

typed_vars:
  | c=typed_var cs=typed_vars {c :: cs}
  | c=typed_var {[c]}
;

vars:
  | c=IDENT cs=vars {c :: cs}
  | c=IDENT {[c]}
  ;

constant:
  | HALT {PHalt}
  | RANDOMBOOL {PRandomBool}
  | TRUE {PBool true}
  | FALSE {PBool false}
  | n=NUMBER {PInt n}
  (* | LSEQPRAN cs=constant_list RSEQPRAN {PSeqLit cs} *)
;

constant_list:
| c=constant SEMICOLON cs=constant_list {c :: cs}
| c=constant {[c]}
;

id_eq_expr_list:
| id=IDENT ASSIGN expr=expr SEMICOLON cs=id_eq_expr_list {(id, expr.y)::cs}
| id=IDENT ASSIGN expr=expr {[(id, expr.y)]}
;

expr_closed:
| NULL {{y = PNull #: None; loc = $startpos}}
| THIS {{y = PThis #: None; loc = $startpos}}
| c=constant {{y = (PConst c) #: None; loc = $startpos}}
| id=typed_var {{y = (Pid id) #: None; loc = $startpos}}
| record=expr_closed DOT field=IDENT {{y = (PField {record = record.y; field}) #: None; loc = $startpos}}
| LBRACKET es=id_eq_expr_list RBRACKET {{y = (PRecord es) #: None; loc = $startpos}}
| LBRACKET es=id_eq_expr_list SEMICOLON RBRACKET {{y = (PRecord es) #: None; loc = $startpos}}
| LET lhs=typed_var ASSIGN rhs=expr SEMICOLON body=expr
  {{y = (PLet {lhs; rhs = rhs.y; body = body.y}) #: None; loc = $startpos}}
| GOTO st=IDENT {{ y = (PGoto st) #: None; loc = $startpos}}
| DEREF e=expr_closed {{ y = (PDeref e.y) #: None; loc = $startpos}}
| NOT e=expr_closed {{y = (PApp {pfunc = ("not" #: None); args = [e.y]}) #: None; loc = $startpos}}
| e1=expr_closed op=biop e2=expr_closed {{y = (PApp {pfunc = (op #: None); args = [e1.y; e2.y]}) #: None; loc = $startpos}}
| LPAR e=expr RPAR {e}
;

expr_list:
| c=expr_closed cs=expr_list {c :: cs}
| c1=expr_closed {[c1]}
;

expr:
| r=expr_closed {r}
| lvalue=expr_closed COLONEQ rvalue=expr {{y = (PAssign {lvalue = lvalue.y; rvalue = rvalue.y}) #: None; loc = $startpos}}
| rhs=expr_closed SEMICOLON body=expr {{y = (PSeq {rhs = rhs.y; body = body.y}) #: None; loc = $startpos}}
| pfunc=typed_var args=expr_list {{y = (PApp {pfunc; args = (_gets args)}) #: None; loc = $startpos}}
;

func_decl:
| params=typed_vars LOCAL local_vars=typed_vars ASSIGN body=expr
  {{y = {params; local_vars; body = mk_return body.y}; loc = $startpos}}
| params=typed_vars ASSIGN body=expr
  {{y = {params; local_vars = []; body = mk_return body.y}; loc = $startpos}}
| LPAR RPAR ASSIGN body=expr
  {{y = {params = []; local_vars = []; body = mk_return body.y}; loc = $startpos}}
;

state_label:
| HOT {Hot}
| COLD {Cold}
| START {Start}
;

state_label_list:
| c=state_label cs=state_label_list {c :: cs}
| c1=state_label {[c1]}
;

func_label:
| PLAIN {Plain}
| ENTRY {Entry}
| EXIT {Exit}
| LISTEN name=IDENT ON {Listen name}
;

labeled_func_list:
| fl=func_label fd=func_decl cs=labeled_func_list {(fl #: None, fd.y):: cs}
| fl=func_label fd=func_decl {[(fl #: None, fd.y)]}
;

named_func_list:
| PLAIN pfunc=IDENT fd=func_decl cs=named_func_list {((pfunc #: None), fd.y):: cs}
| PLAIN pfunc=IDENT fd=func_decl {[((pfunc #: None), fd.y)]}
;

state:
| STATE LSEQPRAN state_label=state_label_list RSEQPRAN name=IDENT LBRACKET state_body=labeled_func_list RBRACKET
  {{y = {name; state_label; state_body}; loc = $startpos}}
| STATE name=IDENT LBRACKET state_body=labeled_func_list RBRACKET
  {{y = {name; state_label = []; state_body}; loc = $startpos}}
;

state_list:
| c=state cs=state_list {c.y :: cs}
| c1=state {[c1.y]}
;

state_list_bracket:
| LBRACKET cs=state_list RBRACKET {cs}
| LBRACKET RBRACKET {[]}
;

machine:
| MACHINEDEF name=IDENT LOCAL local_vars=typed_vars FUNC local_funcs=named_func_list states=state_list_bracket
  {{y = {name; local_vars; local_funcs; states}; loc = $startpos}}
| MACHINEDEF name=IDENT LOCAL local_vars=typed_vars states=state_list_bracket
  {{y = {name; local_vars; local_funcs = []; states}; loc = $startpos}}
| MACHINEDEF name=IDENT FUNC local_funcs=named_func_list states=state_list_bracket
  {{y = {name; local_vars = []; local_funcs; states}; loc = $startpos}}
| MACHINEDEF name=IDENT states=state_list_bracket
  {{y = {name; local_vars = []; local_funcs = []; states}; loc = $startpos}}
;

item:
  | TYPEDEF id=IDENT ASSIGN nt=nt {{y = PTypeDecl (id #: (nt)); loc = $startpos}}
  | TYPEDEF id=IDENT ASSIGN MACHINEDEF {{y = PTypeDecl (id #: (mk_p_abstract_ty "machine")); loc = $startpos}}
  | EVENTDECL id=IDENT COLON nt=nt {{y = PEventDecl (id #: (nt)); loc = $startpos}}
  | FUNCDECL id=biop COLON nt=nt {{y = PPrimFuncDecl (id #: (Some nt)); loc = $startpos}}
  | FUNCDECL id=IDENT COLON nt=nt {{y = PPrimFuncDecl (id #: (Some nt)); loc = $startpos}}
  | m=machine {{y = PMachine m.y; loc = $startpos}}
  | PLAIN pfunc=IDENT fd=func_decl {{y = PGlobalFunc (pfunc #: None, fd.y); loc = $startpos}}
;

item_list:
  | c=item cs=item_list {c :: cs}
  | c=item {[c]}
  ;

prog_eof:
  | s=item_list ; EOF { s }
;
%%

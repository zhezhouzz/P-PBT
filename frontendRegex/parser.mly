%{
    open Past (* open Grammar *)
    open Syntax

    let _get {y; _} = y
         %}

(* tokens *)
(* keywords *)
%token EOF TYPEDEF CONSTDEF SPECDEF MACHINEDEF ASSIGN FUNCDECL EVENTDECL LITDECL LET IN FUNCTION ALL REQUEST RESPONSE ENUM HIDDEN
(* arithmetic operators *)
%token PLUS MINUS STAR DIV LT GT LE GE NEQ EQ
(* logic operators *)
%token NOT AND OR TRUE FALSE IMPL IFF FORALL EXISTS PI
(* splitter *)
%token COLON ARROW COMMA BAR SEMICOLON
(* paranthesis *)
%token LSEQPRAN RSEQPRAN LPAR RPAR LEPAR REPAR
(* regex *)
%token ANY EMP EPSILON CTX REPEAT CONCAT
(* type *)
%token INT BOOL SUBTYPING UNIT PRIME
%token <string> IDENT
%token <string> STRING
%token <int> NUMBER

(* start symbol *)
%start <Past.term> prog_eof
%on_error_reduce statement_list
%%

regex_case:
| op=IDENT ARROW p=prop {{y = normalize_name (EffEvent {op; vs = []; phi = p.y}); loc = $startpos}}
| ALL ARROW p=prop {{y = normalize_name (EffEvent {op = "all"; vs = []; phi = p.y}); loc = $startpos}}
;

regex_case_list:
| c=regex_case BAR cs=regex_case_list {c :: cs}
| c=regex_case {[c]}
;

regex_match:
| FUNCTION BAR cs=regex_case_list {{ y = mk_sevents_from_ses (List.map _get cs); loc = $startpos}}
| FUNCTION cs=regex_case_list {{ y = mk_sevents_from_ses (List.map (fun x ->x.y) cs); loc = $startpos}}
| op=IDENT BAR p=prop {{y = Atomic (normalize_name (EffEvent {op; vs = []; phi = p.y})); loc = $startpos}}
;

regex_base:
  | EMP {{y = EmptyA; loc = $startpos}}
  | EPSILON {{y = EpsilonA; loc = $startpos}}
  | p1=regex_base CONCAT p2=regex_base {{y = SeqA(p1.y, p2.y); loc = $startpos}}
  | p1=regex_base OR p2=regex_base {{y = LorA(p1.y, p2.y); loc = $startpos}}
  | p1=regex_base AND p2=regex_base {{y = LandA(p1.y, p2.y); loc = $startpos}}
  | REPEAT n=NUMBER p=regex_base {{y = RepeatN (n, p.y); loc = $startpos}}
  | r=regex_base STAR {{y = StarA r.y; loc = $startpos}}
  | s=sevent {{y =Atomic s.y; loc = $startpos}}
  | LEPAR r=regex_match REPAR {{y = r.y; loc = $startpos}}
  | r=regex_extention {{y = Extension r.y; loc = $startpos}}
  | r=regex_sugar {{y = SyntaxSugar r.y; loc = $startpos}}
  | LPAR r=regex RPAR {r}
;

regex_extention:
  | ANY {{y = AnyA; loc = $startpos}}
  | NOT p=regex {{y = ComplementA p.y; loc = $startpos}}
  ;

regex_sugar:
  | p1=regex MINUS p2=regex {{y = SetMinusA(p1.y, p2.y); loc = $startpos}}
  | CTX LSEQPRAN op_names=vars RSEQPRAN p=regex {{y = CtxOp {op_names; body = p.y}; loc = $startpos}}
  ;

regex_expr:
  | FORALL LPAR id=IDENT COLON nt=nt RPAR COMMA p=regex {{y = QFRegex {qv = id #: (RForall nt); body = p.y}; loc = $startpos}}
  | EXISTS LPAR id=IDENT COLON nt=nt RPAR COMMA p=regex {{y = QFRegex {qv = id #: (RExists nt); body = p.y}; loc = $startpos}}
  | PI LPAR qv=IDENT SUBTYPING nt=nt RPAR COMMA p=regex {{y = QFRegex {qv = qv #: (RPi nt); body = p.y}; loc = $startpos}}
  | FORALL LPAR qv=IDENT SUBTYPING nt=nt RPAR COMMA p=regex {{y = QFRegex {qv = qv #: (RPi nt); body = p.y}; loc = $startpos}}
  | regex=regex_base {{y = RRegex regex.y; loc = $startpos}}
  | LET lhs=typed_var ASSIGN rhs=regex_expr IN body=regex {{y = RLet {lhs; rhs = rhs.y; body = body.y}; loc = $startpos}}
  | id=typed_var {{y = RVar id; loc = $startpos}}
  | c=constant {{y = RConst c; loc = $startpos}}
  | REPEAT n=IDENT p=regex_base {{y = Repeat (n, p.y); loc = $startpos}}
;

regex_expr_list:
  | c=regex_expr cs=regex_expr_list {c :: cs}
  | c1=regex_expr {[c1]}
  ;

regex:
  | r=regex_base {r}
  | es=regex_expr_list {
           match es with
           | [] -> failwith "die"
           | [r] -> {y = RExpr r.y; loc = $startpos}
           | f :: args ->
              let y = List.fold_left (fun func arg -> RApp {func = RExpr func; arg = arg.y}) f.y args in
              {y = RExpr y; loc = $startpos}
         }
  ;

enum_name_list:
  | c=IDENT BAR cs=enum_name_list {c :: cs}
  | c1=IDENT {[c1]}
  ;


statement:
  | ENUM id=IDENT ASSIGN cs=enum_name_list {{y = MEnumDecl (id, cs); loc = $startpos}}
  | TYPEDEF id=IDENT SUBTYPING nt=nt {{y = MTyDeclSub {type_name = id; super_ty = nt}; loc = $startpos}}
  | LITDECL id=IDENT ASSIGN p=prop {{y = MAxiom {name = id; prop = p.y}; loc = $startpos}}
  | FUNCDECL id=IDENT COLON nt=nt {{y = MValDecl (id #: (Some nt)); loc = $startpos}}
  | FUNCDECL id=STRING COLON nt=nt {{y = MValDecl (id #: (Some nt)); loc = $startpos}}
  | REQUEST EVENTDECL id=IDENT COLON nt=nt {{y = MEventDecl {ev = (id #: (Some nt)); event_kind = Req}; loc = $startpos}}
  | RESPONSE EVENTDECL id=IDENT COLON nt=nt {{y = MEventDecl {ev = (id #: (Some nt)); event_kind = Resp}; loc = $startpos}}
  | HIDDEN EVENTDECL id=IDENT COLON nt=nt {{y = MEventDecl {ev = (id #: (Some nt)); event_kind = Hidden}; loc = $startpos}}
  | TYPEDEF id=IDENT ASSIGN c=constant {{y = MRegex {name = (id #: None); automata = RExpr (RConst c)}; loc = $startpos}}
  | CONSTDEF id=IDENT ASSIGN c=constant {{y = MRegex {name = (id #: None); automata = RExpr (RConst c)}; loc = $startpos}}
  | SPECDEF id=IDENT ASSIGN q=regex {{y = MRegex {name = (id #: None); automata = q.y}; loc = $startpos}}
  | MACHINEDEF id=IDENT ASSIGN q=regex {{y = MRegex {name = (id #: None); automata = q.y}; loc = $startpos}}
  | MACHINEDEF id=IDENT args=typed_vars ASSIGN q=regex {{y = MRegex {name = (id #: None); automata = mk_reg_func args q.y}; loc = $startpos}}
  ;

statement_list:
  | c=statement SEMICOLON cs=statement_list {c :: cs}
  | c=statement {[c]}
  ;


prog_eof:
  | s=statement_list ; EOF { s }
  | s=statement_list SEMICOLON ; EOF { s }
;
%%

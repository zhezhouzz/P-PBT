%{
    open Past (* open Grammar *)
    open Syntax

    let _get {y; _} = y
         %}

(* tokens *)
(* keywords *)
%token EOF TYPE CONST SPEC ASSIGN FUNC EVENT LITDECL LET IN ALL REQUEST RESPONSE ENUM HIDDEN GENERATOR SCOPE AXIOM CONFIG VIOLATION MATCH STEP PCOMMENT ATOM REGEX
(* arithmetic operators *)
%token PLUS MINUS STAR DIV LT GT LE GE NEQ EQ
(* logic operators *)
%token NOT AND OR TRUE FALSE IMPL IFF FORALL EXISTS PI
(* splitter *)
%token COLON CCOLON ARROW COMMA BAR SEMICOLON DOT
(* paranthesis *)
%token LSEQPRAN RSEQPRAN LPAR RPAR LEPAR REPAR LBRACKET RBRACKET
(* regex *)
%token EMP EPSILON CTX REPEAT CONCAT
(* type *)
%token INT BOOL SUBTYPING UNIT PRIME
(* dummy *)
%token SHARP
%token <string> IDENT
%token <string> STRING
%token <int> NUMBER

(* start symbol *)
%start <Past.term> prog_eof
%on_error_reduce statement_list
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
  | LT GT {Nt.Ty_record []}
  | LT ts=type_feilds GT {Nt.Ty_record ts}
  | LT ts=type_feilds SEMICOLON GT {Nt.Ty_record ts}
;

type_feilds:
  | id=IDENT COLON nt=base_nt {[(id, nt)]}
  | id=IDENT COLON nt=base_nt COMMA ts=type_feilds {(id, nt) :: ts}
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
  | DIV {"\\"}
  | LT {"<"}
  | GT {">="}
  | LE {">="}
  | GE {">"}
  | EQ {"=="}
  | NEQ {"!="}
;

typed_var:
  | LPAR id=IDENT COLON nt=nt RPAR {id #: (Some nt)}
  | id=IDENT {id #: None}
  | SHARP id=IDENT {id #: None}
;

typed_vars:
  | c=typed_var cs=typed_vars {c :: cs}
  | c=typed_var {[c]}
;

vars:
  | c=IDENT COMMA cs=vars {c :: cs}
  | c=IDENT {[c]}
  ;

constant:
  | TRUE {B true}
  | FALSE {B false}
  | n=NUMBER {I n}
| LSEQPRAN cs=constant_list RSEQPRAN {SetLiteral cs}
;

  constant_list:
| c=constant SEMICOLON cs=constant_list {c :: cs}
| c=constant {[c]}
;

  lit:
| c=constant {AC c}
| id=typed_var {AVar id}
| l1=typed_lit op=biop l2=typed_lit {AAppOp (op #: (None), [l1; l2])}
| LPAR lit=lit RPAR {lit}
;

  typed_lit:
| LPAR lit=lit COLON nt=nt RPAR {lit #: (Some nt)}
| lit=lit {lit #: (None)}
;

prop:
| p1=prop_base IMPL p2=prop {{y = Implies(p1.y, p2.y); loc = $startpos}}
| p1=prop_base IFF p2=prop {{y = Iff(p1.y, p2.y); loc = $startpos}}
| p1=prop_base OR p2=prop {{y = Or [p1.y; p2.y]; loc = $startpos}}
| p1=prop_base AND p2=prop {{y = And [p1.y; p2.y]; loc = $startpos}}
| p=prop_base {p}
;

prop_base:
| NOT p1=prop {{y = Not(p1.y); loc = $startpos}}
| FORALL qv=typed_var COMMA p=prop {{y = Forall {qv; body = p.y}; loc = $startpos}}
| EXISTS qv=typed_var COMMA p=prop {{y = Exists {qv; body = p.y}; loc = $startpos}}
| l=typed_lit {{y = Lit l; loc = $startpos}}
| LPAR prop=prop RPAR {prop}
;

sevent:
| LEPAR op=IDENT vs=typed_vars BAR p=prop REPAR {{y = (EffEvent {op; vs; phi = p.y}); loc = $startpos}}
;

regex_case:
| op=IDENT ARROW p=prop {{y = (EffEvent {op; vs = []; phi = p.y}); loc = $startpos}}
| ALL ARROW p=prop {{y = (EffEvent {op = "all"; vs = []; phi = p.y}); loc = $startpos}}
;

regex_case_list:
| c=regex_case BAR cs=regex_case_list {c :: cs}
| c=regex_case {[c]}
;

regex_match:
| MATCH BAR cs=regex_case_list {{ y = mk_sevents_from_ses (List.map _get cs); loc = $startpos}}
| MATCH cs=regex_case_list {{ y = mk_sevents_from_ses (List.map (fun x ->x.y) cs); loc = $startpos}}
| op=IDENT BAR p=prop {{y = Atomic ((EffEvent {op; vs = []; phi = p.y})); loc = $startpos}}
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
  | id=typed_var {{y = RExpr (RVar id); loc = $startpos}}
  | LPAR r=regex RPAR {r}
;

regex_extention:
  | DOT {{y = AnyA; loc = $startpos}}
  | NOT p=regex {{y = ComplementA p.y; loc = $startpos}}
  ;

names:
  | LSEQPRAN RSEQPRAN {[]}
  | LSEQPRAN op_names=vars RSEQPRAN {op_names}

regex_sugar:
  | p1=regex DIV p2=regex {{y = SetMinusA(p1.y, p2.y); loc = $startpos}}
  | p1=regex MINUS p2=regex {{y = SetMinusA(p1.y, p2.y); loc = $startpos}}
  | SCOPE op_names=names p=regex {{y = CtxOp {op_names; body = p.y}; loc = $startpos}}
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

enum_elem_list:
  | c=IDENT COMMA cs=enum_elem_list {c :: cs}
  | c1=IDENT {[c1]}
  ;

event_feilds:
  | id=IDENT COLON tp=nt COMMA cs=event_feilds {(id, tp) :: cs}
  | id=IDENT COLON tp=nt {[(id, tp)]}
;

p_event_define:
  | TYPE tyid=IDENT ASSIGN LPAR es=event_feilds RPAR SEMICOLON EVENT id=IDENT COLON tyid2=IDENT
    {if not (String.equal tyid tyid2) then failwith "invalid event declear" else id #: (Nt.Ty_record es)}
  | EVENT id=IDENT COLON  LPAR es=event_feilds RPAR
    {id #: (Nt.Ty_record es)}
;

op_names:
  | c=IDENT BAR cs=op_names {c :: cs}
  | id=IDENT {[id]}
  ;

atom:
  | ATOM LPAR id=IDENT COLON ops=op_names RPAR CCOLON p=prop SEMICOLON
    {(id #: (Some mk_p_regex_ty), MultiAtomic (List.map (fun op -> EffEvent {op; vs = []; phi = p.y}) ops))}
;

spec:
  | REGEX r=regex SEMICOLON {r}
  | REGEX r=regex {r}
  | a=atom r=spec {{y = RExpr (RLet {lhs = (fst a); rhs = RRegex (snd a); body = r.y}); loc = $startpos}}
;

generator_filed:
  | SCOPE ASSIGN event_scope=names SEMICOLON {{y = EventScope event_scope; loc = $startpos}}
  | AXIOM ASSIGN axioms=names SEMICOLON {{y = Axioms axioms; loc = $startpos}}
  | CONFIG ASSIGN type_configs=names SEMICOLON {{y = TypeConfigs type_configs; loc = $startpos}}
  | VIOLATION ASSIGN violation=IDENT SEMICOLON {{y = Violation violation; loc = $startpos}}
  | STEP ASSIGN step_bound=NUMBER SEMICOLON {{y = StepBound step_bound; loc = $startpos}}
;

generator_fileds:
  | c=generator_filed cs=generator_fileds {c :: cs}
  | id=generator_filed {[id]}
  ;

pcomment:
  | PCOMMENT REQUEST {Req}
  | PCOMMENT RESPONSE {Resp}
  | PCOMMENT HIDDEN {Hidden}
;

statement:
  | ENUM enum_name=IDENT LBRACKET enum_elems=enum_elem_list RBRACKET {{y = MAbstractType (enum_name #: (CEnumType {enum_name; enum_elems})); loc = $startpos}}
  | TYPE id=IDENT ASSIGN superty=nt SEMICOLON {{y = MAbstractType (id #: (CBaseType {superty; use_config = false})); loc = $startpos}}
  | FUNC id=STRING COLON nt=nt SEMICOLON {{y = MValDecl (id #: nt); loc = $startpos}}
  | REQUEST EVENT id=IDENT COLON nt=nt SEMICOLON {{y = MEventDecl {ev = (id #: nt); event_kind = Req}; loc = $startpos}}
  | RESPONSE EVENT id=IDENT COLON nt=nt SEMICOLON {{y = MEventDecl {ev = (id #: nt); event_kind = Resp}; loc = $startpos}}
  | HIDDEN EVENT id=IDENT COLON nt=nt SEMICOLON {{y = MEventDecl {ev = (id #: nt); event_kind = Hidden}; loc = $startpos}}

  | event_kind=pcomment ev=p_event_define SEMICOLON {{y = MEventDecl {ev; event_kind}; loc = $startpos}}
  | PCOMMENT ev_name=IDENT DOT field=IDENT ASSIGN assignment =IDENT {{y = MFieldAssign {field = deparse_field ev_name field; assignment }; loc = $startpos}}

  | SPEC id=IDENT LBRACKET q=spec RBRACKET {{y = MRegex {name = (id #: mk_p_regex_ty); automata = q.y}; loc = $startpos}}
  | SPEC id=IDENT args=typed_vars LBRACKET q=spec RBRACKET {{y = MRegex {name = (id #: (mk_regex_func_type args)); automata = mk_reg_func args q.y}; loc = $startpos}}
  | GENERATOR client_name=IDENT LBRACKET gs=generator_fileds RBRACKET {{y = parse_client client_name (List.map (fun x -> x.y) gs); loc = $startpos}}
  ;

statement_list:
  | c=statement cs=statement_list {c :: cs}
  | c=statement {[c]}
  ;

prog_eof:
  | s=statement_list ; EOF { s }
  | s=statement_list SEMICOLON ; EOF { s }
;
%%

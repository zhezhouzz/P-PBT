open Ast
open Zdatatype

let layout_sexp_regex regex =
  Sexplib.Sexp.to_string
  @@ sexp_of_regex
       (fun _ -> Sexplib.Sexp.unit)
       (sexp_of_sevent (fun _ -> Sexplib.Sexp.unit))
       regex

let rec rexpr_to_lit = function
  | RConst c -> Some (AC c)
  | RVar var -> Some (AVar var)
  | RRegex (RExpr r) -> rexpr_to_lit r
  | _ -> None

let _subst_se name (m : ('t, 't sevent) regex_expr) se =
  (* let () = *)
  (*   Printf.printf "\tsubst %s --> %s in %s\n" name *)
  (*     (layout_sexp_regex (RExpr m)) *)
  (*     (layout_sexp_regex (Atomic se)) *)
  (* in *)
  match rexpr_to_lit m with
  | Some lit -> Sevent.subst_sevent_instance name lit se
  | None -> se

let rec subst_regex regex name (m : ('t, 't sevent) regex_expr) =
  let rec aux regex =
    match regex with
    | EmptyA | EpsilonA -> regex
    | Atomic se -> Atomic (_subst_se name m se)
    | RepeatN (n, r) -> RepeatN (n, subst_regex r name m)
    | MultiAtomic ses -> MultiAtomic (List.map (_subst_se name m) ses)
    | LorA (r1, r2) -> LorA (aux r1, aux r2)
    | LandA (r1, r2) -> LandA (aux r1, aux r2)
    | SeqA (r1, r2) -> SeqA (aux r1, aux r2)
    | StarA r -> StarA (aux r)
    | DComplementA { atoms; body } ->
        DComplementA
          { atoms = List.map (_subst_se name m) atoms; body = aux body }
    | Extension r -> Extension (subst_regex_extension r name m)
    | SyntaxSugar r -> SyntaxSugar (subst_regex_sugar r name m)
    | RExpr r -> RExpr (subst_regex_expr r name m)
  in
  aux regex

and subst_regex_extension regex name (m : ('t, 't sevent) regex_expr) =
  match regex with
  | AnyA -> AnyA
  | ComplementA r -> ComplementA (subst_regex r name m)
  | Ctx { atoms; body } ->
      Ctx
        {
          atoms = List.map (_subst_se name m) atoms;
          body = subst_regex body name m;
        }

and subst_regex_sugar regex name (m : ('t, 't sevent) regex_expr) :
    ('t, 'b) regex_sugar =
  match regex with
  | CtxOp { op_names; body } ->
      CtxOp { op_names; body = subst_regex body name m }
  | SetMinusA (r1, r2) ->
      SetMinusA (subst_regex r1 name m, subst_regex r2 name m)

and subst_regex_expr regex name (m : ('t, 't sevent) regex_expr) :
    ('t, 'b) regex_expr =
  let rec aux regex =
    match regex with
    | RRegex r -> RRegex (subst_regex r name m)
    | Repeat (x, r) when String.equal name x -> (
        match rexpr_to_lit m with
        | Some (AVar y) -> Repeat (y.x, subst_regex r name m)
        | Some (AC (I n)) -> RRegex (RepeatN (n, subst_regex r name m))
        | _ -> Repeat (x, subst_regex r name m))
    | Repeat (x, r) -> Repeat (x, subst_regex r name m)
    | RVar x -> if String.equal x.x name then m else RVar x
    | RConst c -> RConst c
    | QFRegex { qv; body } ->
        let qv =
          match qv.ty with
          | RForall ty when String.equal name @@ Nt.layout ty ->
              let c = match m with RConst c -> c | _ -> _die [%here] in
              qv.x #: (RForallC c)
          | RExists ty when String.equal name @@ Nt.layout ty ->
              let c = match m with RConst c -> c | _ -> _die [%here] in
              qv.x #: (RExistsC c)
          | _ -> qv
        in
        if String.equal qv.x name then regex
        else QFRegex { qv; body = subst_regex body name m }
    | RApp { func; arg } ->
        RApp { func = subst_regex func name m; arg = aux arg }
    | RLet { lhs; rhs; body } ->
        RLet { lhs; rhs = aux rhs; body = subst_regex body name m }
  in
  aux regex

let labels_to_multiatomic ls =
  let ls = List.slow_rm_dup (fun a b -> 0 == Stdlib.compare a b) ls in
  match ls with [] -> EmptyA | [ e ] -> Atomic e | _ -> MultiAtomic ls

let ses_to_regex = function
  | [] -> EmptyA
  | [ s ] -> Atomic s
  | ss -> MultiAtomic ss

open Sevent

(** eliminate syntax sugar *)

let rec desugar ctx regex =
  match regex with
  | RExpr (RRegex r) -> desugar ctx r
  | RExpr _ ->
      let () = Printf.printf "%s\n" (layout_sexp_regex regex) in
      _failatwith [%here]
        (spf "should be eliminated: %s" (layout_sexp_regex regex))
  | Extension r -> Extension (desugar_regex_extension ctx r)
  | SyntaxSugar (SetMinusA (r1, r2)) ->
      desugar ctx
        (LandA (desugar ctx r1, Extension (ComplementA (desugar ctx r2))))
  | SyntaxSugar (CtxOp { op_names; body }) ->
      let atoms =
        List.map
          (fun op_name ->
            match get_opt ctx.event_tyctx op_name with
            | None ->
                _failatwith [%here] (spf "event(%s) is not declared" op_name)
            | Some ty -> mk_top_sevent op_name ty)
          op_names
      in
      desugar ctx (Extension (Ctx { atoms; body }))
  | EmptyA | EpsilonA | Atomic _ | MultiAtomic _ -> regex
  | LorA (r1, r2) -> (
      match (desugar ctx r1, desugar ctx r2) with
      | EmptyA, r2 -> r2
      | r1, EmptyA -> r1
      | r1, r2 -> LorA (r1, r2))
  | LandA (r1, r2) -> (
      match (desugar ctx r1, desugar ctx r2) with
      | EmptyA, _ | _, EmptyA -> EmptyA
      | r1, r2 -> LandA (r1, r2))
  | RepeatN (n, r) -> RepeatN (n, desugar ctx r)
  | SeqA (r1, r2) -> SeqA (desugar ctx r1, desugar ctx r2)
  | StarA r -> StarA (desugar ctx r)
  | DComplementA { atoms; body } ->
      DComplementA { atoms; body = desugar ctx body }

and desugar_regex ctx r = desugar ctx r

and desugar_regex_extension ctx regex =
  match regex with
  | AnyA -> AnyA
  | ComplementA r -> ComplementA (desugar_regex ctx r)
  | Ctx { atoms; body } -> Ctx { atoms; body = desugar_regex ctx body }

(** eliminate extension *)
let delimit_context (delimit_cotexnt_char : 'a list option * 'a -> 'a list)
    (regex : ('t, 'a) regex) : ('t, 'a) regex =
  let ctx, regex =
    match regex with
    | Extension (Ctx { atoms; body }) -> (Some atoms, body)
    | _ -> (None, regex)
  in
  let force_ctx = function
    | None ->
        _failatwith [%here]
          "the regex need to be quantified with a context of chars."
    | Some ctx -> ctx
  in
  let rec aux ctx regex =
    match regex with
    | RExpr _ | SyntaxSugar _ -> _die_with [%here] "should be eliminated"
    | Extension (ComplementA EmptyA) -> StarA (MultiAtomic (force_ctx ctx))
    | Extension (ComplementA EpsilonA) ->
        SeqA (MultiAtomic (force_ctx ctx), StarA (MultiAtomic (force_ctx ctx)))
    | Extension (ComplementA r) ->
        DComplementA { atoms = force_ctx ctx; body = aux ctx r }
    | Extension AnyA -> MultiAtomic (force_ctx ctx)
    | Extension (Ctx { atoms; body }) ->
        let atoms =
          List.slow_rm_dup (fun a b -> 0 == Stdlib.compare a b) atoms
        in
        aux (Some atoms) body
    | Atomic e -> ses_to_regex @@ delimit_cotexnt_char (ctx, e)
    | MultiAtomic es ->
        ses_to_regex @@ List.concat
        @@ List.map (fun e -> delimit_cotexnt_char (ctx, e)) es
    | EmptyA | EpsilonA -> regex
    | RepeatN (n, r) -> RepeatN (n, aux ctx r)
    | DComplementA { atoms; body } ->
        DComplementA { atoms; body = aux (Some atoms) body }
    | LorA (r1, r2) -> LorA (aux ctx r1, aux ctx r2)
    | LandA (r1, r2) -> LandA (aux ctx r1, aux ctx r2)
    | SeqA (r1, r2) -> SeqA (aux ctx r1, aux ctx r2)
    | StarA r -> StarA (aux ctx r)
  in
  aux ctx regex

let gather_regex regex =
  let rec aux regex m =
    match regex with
    | RExpr _ | SyntaxSugar _ | Extension _ ->
        _die_with [%here] "should be eliminated"
    | RepeatN (_, r) -> aux r m
    | EmptyA -> m
    | EpsilonA -> m
    | Atomic se -> Sevent.gather_se m se
    | LorA (t1, t2) -> aux t1 @@ aux t2 m
    | LandA (t1, t2) -> aux t1 @@ aux t2 m
    | SeqA (t1, t2) -> aux t1 @@ aux t2 m
    | StarA t -> aux t m
    | MultiAtomic se -> List.fold_left Sevent.gather_se m se
    | DComplementA { atoms; body } ->
        let m = List.fold_left Sevent.gather_se m atoms in
        aux body m
  in
  aux regex (Sevent.gathered_lits_init ())

let lift_function e =
  let rec aux f r =
    match r with
    | RExpr (RRegex r) -> aux f r
    | RExpr (QFRegex { qv; body }) -> (
        match qv.ty with
        | RForall _ | RPi _ -> None
        | _ -> aux (fun body -> RExpr (QFRegex { qv; body = f body })) body)
    | _ as r -> Some (f, r)
  in
  aux (fun x -> x) e

let regex_is_function e : bool =
  let rec aux r =
    match r with
    | RExpr (RRegex r) -> aux r
    | RExpr (QFRegex { qv; body }) -> (
        match qv.ty with RForall _ | RPi _ -> true | _ -> aux body)
    | _ -> false
  in
  aux e

let mk_sevent_from_se = function
  | EffEvent { op; phi; vs } as e ->
      if String.equal op "all" then GuardEvent { vs; phi } else e
  | _ -> _die [%here]

let rec mk_lorA = function
  | [] -> EmptyA
  | [ r ] -> r
  | r :: rs -> LorA (r, mk_lorA rs)

let rec mk_landA = function
  | [] -> Extension AnyA
  | [ r ] -> r
  | r :: rs -> LandA (r, mk_landA rs)

let mk_sevents_from_ses ses =
  let all_events, or_events =
    List.partition (function EffEvent _ -> true | GuardEvent _ -> false)
    @@ List.map mk_sevent_from_se ses
  in
  let all_events = List.map (fun e -> Atomic e) all_events in
  mk_lorA (ses_to_regex or_events :: all_events)

let simp_regex (eq : 'a -> 'a -> bool) (regex : ('t, 'a) regex) =
  let mk_multiatom ses =
    (* let () = *)
    (*   Printf.printf "%i = len(%s)\n" (List.length ses) *)
    (*     (layout_sexp_regex (MultiAtomic ses)) *)
    (* in *)
    let ses = List.slow_rm_dup eq ses in
    match ses with [] -> EmptyA | _ -> MultiAtomic ses
  in
  let rec aux regex =
    (* let () = Printf.printf "simp: %s\n" @@ layout_sexp_regex regex in *)
    match regex with
    | RExpr _ | SyntaxSugar _ | Extension _ ->
        _die_with [%here] "should be eliminated"
    | RepeatN (n, r) -> RepeatN (n, aux r)
    | EmptyA -> EmptyA
    | EpsilonA -> EpsilonA
    | Atomic se -> mk_multiatom [ se ]
    | MultiAtomic se -> mk_multiatom se
    | LorA (r1, r2) -> (
        match (aux r1, aux r2) with
        | EmptyA, r | r, EmptyA -> r
        | MultiAtomic r1, MultiAtomic r2 -> aux (MultiAtomic (r1 @ r2))
        | r1, r2 -> LorA (r1, r2))
    | LandA (r1, r2) -> (
        match (aux r1, aux r2) with
        | EmptyA, _ | _, EmptyA -> EmptyA
        | MultiAtomic r1, MultiAtomic r2 ->
            aux (MultiAtomic (List.interset eq r1 r2))
        | r1, r2 -> LandA (r1, r2))
    | SeqA (r1, r2) -> (
        match (aux r1, aux r2) with
        | EpsilonA, r | r, EpsilonA -> r
        | r1, r2 -> SeqA (r1, r2))
    | StarA r -> (
        match aux r with
        | EmptyA -> EpsilonA
        | EpsilonA -> EpsilonA
        | r -> StarA r)
    | DComplementA { atoms; body } -> (
        let atoms = List.slow_rm_dup eq atoms in
        let any_r = mk_multiatom atoms in
        match aux body with
        | EmptyA -> StarA any_r
        | EpsilonA -> LorA (any_r, SeqA (any_r, StarA any_r))
        | body -> DComplementA { atoms; body })
  in
  aux regex

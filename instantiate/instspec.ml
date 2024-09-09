open Language
open Zdatatype

type rexpr = (Nt.t, Nt.t sevent) regex_expr

(** Eta-redunction all specification in the given file*)

let rec eta_reduction_regex_expr (ctx : rexpr ctx) (inst : rexpr) : rexpr =
  let rec aux ctx = function
    | RRegex r -> RRegex (eta_reduction_regex ctx r)
    | RVar name ->
        (* in eta reduction, we allow unbound variables. *)
        let res =
          match get_opt ctx name.x with Some res -> res | None -> RVar name
        in
        res
    | RConst _ as r -> r
    | RLet { lhs; rhs; body } ->
        let rhs = aux ctx rhs in
        let body = subst_regex body lhs.x rhs in
        (* let ctx = add_to_right ctx lhs.x #: rhs in *)
        let body = eta_reduction_regex ctx body in
        let body = instantiate_function ctx body in
        (* let () = *)
        (*   Printf.printf "instantiate: %s\n" @@ layout_symbolic_regex body *)
        (* in *)
        RRegex body
    | RApp { func; arg } ->
        let func = eta_reduction_regex ctx func in
        (* let () = Printf.printf "func: %s\n" @@ layout_symbolic_regex func in *)
        let arg = aux ctx arg in
        (* let () = *)
        (*   Printf.printf "arg: %s\n" @@ layout_symbolic_regex (RExpr arg) *)
        (* in *)
        let res = do_apply ctx func arg in
        (* let () = Printf.printf "app: %s\n" @@ layout_symbolic_regex res in *)
        RRegex (eta_reduction_regex ctx res)
    | QFRegex { qv; body } ->
        QFRegex { qv; body = eta_reduction_regex ctx body }
    | Repeat (x, r) -> (
        let r = eta_reduction_regex ctx r in
        match get_opt ctx x with
        | None -> Repeat (x, r)
        | Some (RConst (I m)) -> RRegex (RepeatN (m, r))
        | Some (RVar y) -> Repeat (y.x, r)
        | _ -> _die_with [%here] (spf "wrong defined %s" x))
  in
  aux ctx inst

and instantiate_function ctx = function
  | RExpr (RRegex r) -> instantiate_function ctx r
  | RExpr (QFRegex { qv; body }) ->
      let qv =
        match qv.ty with
        | RForall ty -> (
            match get_opt ctx (Nt.layout ty) with
            | Some m ->
                let c = match m with RConst c -> c | _ -> _die [%here] in
                qv.x #: (RForallC c)
            | None -> qv)
        | RExists ty -> (
            match get_opt ctx (Nt.layout ty) with
            | Some m ->
                let c = match m with RConst c -> c | _ -> _die [%here] in
                qv.x #: (RExistsC c)
            | None -> qv)
        | _ -> qv
      in
      RExpr (QFRegex { qv; body = instantiate_function ctx body })
  | _ as r -> r

and do_apply ctx (func : (Nt.t, Nt.t sevent) regex) arg =
  match func with
  | RExpr (RRegex r) -> do_apply ctx r arg
  | RExpr (RVar name) -> (
      match get_opt ctx name.x with
      | None -> _die [%here]
      | Some func -> do_apply ctx (RExpr func) arg)
  | RExpr (QFRegex { qv; body }) -> (
      match qv.ty with
      | RForall _ | RPi _ ->
          (* let () = *)
          (*   Printf.printf "subst %s --> %s in %s\n" qv.x *)
          (*     (layout_symbolic_regex (RExpr arg)) *)
          (*     (layout_symbolic_regex body) *)
          (* in *)
          subst_regex body qv.x arg
      | _ ->
          let body = do_apply ctx body arg in
          RExpr (QFRegex { qv; body }))
  | _ ->
      let () = Printf.printf "bad func: %s\n" @@ layout_symbolic_regex func in
      _die [%here]

and eta_reduction_regex_extension (ctx : rexpr ctx)
    (regex : (Nt.t, Nt.t sevent) regex_extension) :
    (Nt.t, Nt.t sevent) regex_extension =
  match regex with
  | AnyA -> AnyA
  | ComplementA r -> ComplementA (eta_reduction_regex ctx r)
  | Ctx { atoms; body } -> Ctx { atoms; body = eta_reduction_regex ctx body }

and eta_reduction_regex_sugar (ctx : rexpr ctx)
    (regex : (Nt.t, Nt.t sevent) regex_sugar) : (Nt.t, Nt.t sevent) regex_sugar
    =
  match regex with
  | CtxOp { op_names; body } ->
      CtxOp { op_names; body = eta_reduction_regex ctx body }
  | SetMinusA (r1, r2) ->
      SetMinusA (eta_reduction_regex ctx r1, eta_reduction_regex ctx r2)

and eta_reduction_regex (ctx : rexpr ctx) (regex : (Nt.t, Nt.t sevent) regex) :
    (Nt.t, Nt.t sevent) regex =
  let rec aux ctx regex =
    match regex with
    | EmptyA | EpsilonA | Atomic _ | MultiAtomic _ -> regex
    | RepeatN (n, r) ->
        let r = aux ctx r in
        RepeatN (n, r)
    | DComplementA { atoms; body } ->
        let body = aux ctx body in
        DComplementA { atoms; body }
    | LorA (r1, r2) -> LorA (aux ctx r1, aux ctx r2)
    | LandA (r1, r2) -> LandA (aux ctx r1, aux ctx r2)
    | SeqA (r1, r2) -> SeqA (aux ctx r1, aux ctx r2)
    | StarA r -> StarA (aux ctx r)
    | Extension r -> Extension (eta_reduction_regex_extension ctx r)
    | SyntaxSugar r -> SyntaxSugar (eta_reduction_regex_sugar ctx r)
    | RExpr r -> RExpr (eta_reduction_regex_expr ctx r)
  in
  aux ctx regex

let eta_reduction_item (ctx : rexpr ctx) (e : Nt.t item) : rexpr ctx =
  match e with
  | MFieldAssign _ | MEventDecl _ | MValDecl _ | MAbstractType _ | MClient _ ->
      ctx
  | MRegex { name; automata } -> (
      match automata with
      | RExpr r ->
          let res = normalize_regex_expr @@ eta_reduction_regex_expr ctx r in
          (* let () = Printf.printf "%s\n" (layout_symbolic_regex (RExpr res)) in *)
          add_to_right ctx name.x #: res
      | _ -> add_to_right ctx name.x #: (RRegex automata))

let eta_reduction_items (ctx : rexpr ctx) (es : Nt.t item list) : rexpr ctx =
  List.fold_left (fun ctx e -> eta_reduction_item ctx e) ctx es

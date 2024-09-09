open Language
open Zdatatype

let const_to_p_const = function
  | U -> PUnit
  | B b -> PBool b
  | I i -> PInt i
  | SetLiteral _ -> _die [%here]
  | _ -> _die [%here]

let rec typed_lit_to_p_expr lit = (lit_to_p_expr lit.x) #: lit.ty

and lit_to_p_expr = function
  | AC c -> PConst (const_to_p_const c)
  | AVar id -> Pid id
  | AAppOp (op, args) ->
      let args = List.map typed_lit_to_p_expr args in
      PApp { pfunc = op; args }
  | _ -> _die [%here]

let prop_to_p_prop p =
  let rec aux = function
    | Lit lit -> typed_lit_to_p_expr lit
    | Implies (a, b) -> aux (Or [ Not a; b ])
    | Ite (a, b, c) -> aux (Or [ And [ a; b ]; And [ Not a; c ] ])
    | Not a -> mk_p_not (aux a)
    | And es -> (
        match List.map aux es with
        | [] -> mk_p_bool true
        | [ e ] -> e
        | e :: es ->
            List.fold_left
              (fun res e ->
                mk_p_app
                  "&&"
                  #: (Nt.construct_arr_tp
                        ([ Nt.Ty_bool; Nt.Ty_bool ], Nt.Ty_bool))
                  [ res; e ])
              e es)
    | Or es -> (
        match List.map aux es with
        | [] -> mk_p_bool false
        | [ e ] -> e
        | e :: es ->
            List.fold_left
              (fun res e ->
                mk_p_app
                  "||"
                  #: (Nt.construct_arr_tp
                        ([ Nt.Ty_bool; Nt.Ty_bool ], Nt.Ty_bool))
                  [ res; e ])
              e es)
    | Iff (a, b) ->
        mk_p_app
          "==" #: (Nt.construct_arr_tp ([ Nt.Ty_bool; Nt.Ty_bool ], Nt.Ty_bool))
          [ aux a; aux b ]
    | _ -> _die [%here]
  in
  aux p

let prop_func_name namespace (op, i) = spf "%s_prop_%s_%i" namespace op i

let compute_qvs_from_prop (vs, prop) =
  let fvars =
    List.slow_rm_dup (fun x y -> String.equal x.x y.x) @@ fv_prop prop
  in
  let fvars =
    List.filter
      (fun v -> not (List.exists (fun x -> String.equal x.x v.x) vs))
      fvars
  in
  fvars

let _mk_p_prop_function_decl (vs, prop) =
  match vs with
  | [] -> None
  | _ ->
      let input = input_name #: (mk_p_record_ty vs) in
      let prepare =
        List.map
          (fun v -> mk_p_assign (mk_pid v, mk_field (mk_pid input) v.x))
          vs
      in
      let qvs = compute_qvs_from_prop (vs, prop) in
      Some
        {
          params = qvs @ [ input ];
          local_vars = vs;
          body = mk_p_seqs prepare (mk_return @@ prop_to_p_prop prop);
        }

type pprop = string * int * (Nt.t, string) typed list * Nt.t prop

let global_prop_func_decl namespace i =
  (prop_func_name namespace (global_event_name, i)) #: Nt.Ty_bool

let _mk_p_global_prop_function_decl namespace i prop =
  ( global_prop_func_decl namespace i,
    {
      params = compute_qvs_from_prop ([], prop);
      local_vars = [];
      body = mk_return @@ prop_to_p_prop prop;
    } )

let prop_func_decl namespace (op, i) =
  let vs =
    match op.ty with
    | Nt.Ty_unit -> []
    | Nt.Ty_record l -> l
    | _ -> _die [%here]
  in
  let vsty = List.map snd vs in
  (prop_func_name namespace (op.x, i))
  #: (Nt.construct_arr_tp (vsty, Nt.Ty_bool))

let mk_prop_func_decl namespace (op, i, vs, prop) =
  let* decl = _mk_p_prop_function_decl (vs, prop) in
  Some ((prop_func_name namespace (op, i)) #: Nt.Ty_bool, decl)

let mk_gprop_func_decl namespace (_, i, _, prop) =
  _mk_p_global_prop_function_decl namespace i prop

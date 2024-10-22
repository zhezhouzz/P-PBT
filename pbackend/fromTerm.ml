open Language
open Ast
open Astbuilder
open Zdatatype

let compile_const = function
  | U -> PUnit
  | B b -> PBool b
  | I i -> PInt i
  | Enum { elem; _ } -> PEnum elem
  | SetLiteral _ -> _die [%here]
  | _ -> _die [%here]

let rec compile_typed_lit lit = (compile_lit lit.x) #: lit.ty

and compile_lit = function
  | AC c -> PConst (compile_const c)
  | AVar id -> Pid id
  | AAppOp (op, args) ->
      let args = List.map compile_typed_lit args in
      PApp { pfunc = op; args }
  | _ -> _die [%here]

let compile_prop p =
  let rec aux = function
    | Lit lit -> compile_typed_lit lit
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

let compile_value x =
  let res =
    match x.x with VConst c -> PConst (compile_const c) | VVar x -> Pid x
  in
  res #: x.ty
(* let assume_function_name = "assume_loop" *)

let mk_p_assert term =
  if Nt.equal_nt Nt.Ty_bool term.ty then (PAssert term) #: Nt.Ty_unit
  else _die_with [%here] "wrong assert"

let mk_p_while body = (PWhile { body }) #: Nt.Ty_int

let mk_sample_space_decl nt =
  let actual_type = match nt with Nt.Ty_bool -> Nt.Ty_bool | _ -> Nt.Ty_int in
  let name = spf "domain_%s" (Nt.layout nt) in
  let decl = name #: (mk_p_set_ty actual_type) in
  decl

let handle_assume vars prop =
  let f var =
    let domain = mk_pid (mk_sample_space_decl var.ty) in
    mk_p_assign (mk_pid var, mk_p_choose domain)
  in
  let cond = compile_prop prop in
  let body = mk_p_seqs_ (List.map f vars @ [ mk_p_it cond mk_p_break ]) in
  mk_p_while body

module TVSet = Rawdesym.TVSet

let get_vars_from_term e =
  let rec aux set e =
    match e.x with
    | CVal _ -> set
    | CLetE { lhs; body; _ } -> aux (TVSet.add_seq (List.to_seq lhs) set) body
    | _ -> set
  in
  let tvars = aux TVSet.empty e in
  List.of_seq @@ TVSet.to_seq tvars

let erase_obs env =
  let rec aux e =
    match e.x with
    | CVal _ -> e
    | CLetE { lhs; rhs = { x = CObs { op; prop }; _ } as rhs; body } ->
        if _get_force [%here] env.recvable_ctx op.x then
          (CLetE { lhs; rhs; body = aux body }) #: e.ty
        else if List.length lhs == 0 then aux body
        else
          let nts = List.map _get_ty lhs in
          (CLetE
             {
               lhs;
               rhs = (CAssume (nts, prop)) #: (Nt.Ty_tuple nts);
               body = aux body;
             })
          #: e.ty
    | CLetE { lhs; rhs; body } -> (CLetE { lhs; rhs; body = aux body }) #: e.ty
    | _ -> _die_with [%here] "unimp"
  in
  aux

let _default_input_name = "input"
let recv_input_name op ty = (spf "input_%s" op) #: ty
let send_function_decl op = (spf "send_%s" op) #: Nt.Ty_unit
let dest_decl = "setting" #: mk_p_machine_ty
let cast_decl op ty = (spf "cast_%s" op) #: ty

let mk_wrapper_send op payload =
  match payload.x with
  | PRecord [] ->
      mk_p_app (send_function_decl op) [ mk_p_self; mk_pid dest_decl ]
  | _ ->
      mk_p_app (send_function_decl op) [ mk_p_self; mk_pid dest_decl; payload ]

let mk_cast_op input op raw_input =
  mk_p_assign
    (mk_pid input, mk_p_app (cast_decl op input.ty) [ mk_pid raw_input ])

let compile_term env e =
  let rec aux e =
    match e.x with
    | CVal v -> compile_value v
    | CLetE { lhs; rhs = { x = CAssume (_, prop); _ }; body } ->
        let loop_expr = handle_assume lhs prop in
        mk_p_seq loop_expr (aux body)
    | CLetE { lhs = []; rhs = { x = CAssertP prop; _ }; body } ->
        mk_p_seq (mk_p_assert (compile_prop prop)) (aux body)
    | CLetE { lhs = []; rhs = { x = CGen { op; args }; _ }; body } ->
        (* let _, dest = StrMap.find "never" env.component_table op.x in *)
        let fields = StrMap.find "never" env.event_tyctx op.x in
        (* let dest = mk_pid dest #: mk_p_machine_ty in *)
        let payload =
          mk_p_record
          @@ _safe_combine [%here] (List.map _get_x fields)
               (List.map compile_value args)
        in
        (* let send_stmt = mk_p_send dest op.x payload in *)
        let send_stmt = mk_wrapper_send op.x payload in
        mk_p_seq send_stmt (aux body)
    | CLetE { lhs; rhs = { x = CObs { op; prop }; _ }; body } -> (
        (* let () = Pp.printf "@{<bold>CObs: %s@}\n" op.x in *)
        (* let () = *)
        (*   StrMap.iter *)
        (*     (fun name ty -> Printf.printf "%s\n" (layout_qv name #: ty)) *)
        (*     env.p_tyctx *)
        (* in *)
        let raw_input_ty = StrMap.find "never" env.p_tyctx op.x in
        let raw_input = _default_input_name #: raw_input_ty in
        match raw_input_ty with
        | Nt.Ty_unit ->
            let recv_stmt = mk_p_recv op.x raw_input mk_p_break in
            mk_p_seq recv_stmt
              (mk_p_seq (mk_p_assert (compile_prop prop)) (aux body))
        | _ty ->
            let fields = StrMap.find "never" env.event_tyctx op.x in
            let input = recv_input_name op.x (mk_p_record_ty fields) in
            let recv_body =
              List.map (fun (x, field) ->
                  mk_p_assign (mk_pid x, mk_p_field (mk_pid input) field.x))
              @@ _safe_combine [%here] lhs fields
            in
            let cast_stmt = mk_cast_op input op.x raw_input in
            let recv_body = mk_p_seqs_ (cast_stmt :: recv_body) in
            let recv_stmt = mk_p_recv op.x raw_input recv_body in
            mk_p_seq recv_stmt
              (mk_p_seq (mk_p_assert (compile_prop prop)) (aux body)))
    | _ -> _die_with [%here] "unimp"
  in
  (* let vars = get_vars_from_term e in *)
  (* let () = Pp.printf "@{<bold>Vars:@}:\n%s\n" (layout_qvs vars) in *)
  let e = erase_obs env e in
  let () = Pp.printf "@{<bold>After Erase Obs:@}:\n%s\n" (layout_term e.x) in
  let body = aux e in
  let () =
    Pp.printf "@{<bold>P Expr:@}:\n%s\n" (Toplang.layout_p_expr env 0 body.x)
  in
  body

let init_state func =
  {
    name = init_state_name;
    state_label = [ Start ];
    state_body = [ (Entry #: Nt.Ty_unit, func) ];
  }

let mk_syn_state func =
  {
    name = "Syn";
    state_label = [ Start ];
    state_body = [ (Entry #: Nt.Ty_unit, func) ];
  }

let mk_syn_machine state =
  { name = "SynClient"; local_vars = []; local_funcs = []; states = [ state ] }

let get_sampling_types env =
  let l =
    StrMap.fold (fun _ l res -> List.map _get_ty l @ res) env.event_tyctx []
  in
  let l = List.filter (function Nt.Ty_enum _ -> false | _ -> true) l in
  let l = List.slow_rm_dup Nt.equal_nt l in
  List.sort Nt.compare_nt l

let compile_syn_result p_tyctx (env : syn_env) e =
  (* let component_table = *)
  (*   StrMap.from_kv_list *)
  (*     [ *)
  (*       ("readReq", ("Client", "Coordinator")); *)
  (*       ("getReq", ("Coordinator", "Database")); *)
  (*       ("readRsp", ("Database", "Client")); *)
  (*       ("writeReq", ("Client", "Coordinator")); *)
  (*       ("putReq", ("Coordinator", "Database")); *)
  (*       ("putRsp", ("Database", "Coordinator")); *)
  (*       ("writeRsp", ("Coordinator", "Client")); *)
  (*       ("commit", ("Coordinator", "Database")); *)
  (*       ("abort", ("Coordinator", "Database")); *)
  (*     ] *)
  (* in *)
  (* let types = *)
  (*   [ Nt.Ty_int; Nt.Ty_bool; mk_p_abstract_ty "pid"; mk_p_abstract_ty "aid" ] *)
  (* in *)
  (* let sampling_space = *)
  (*   List.fold_right *)
  (*     (fun nt -> *)
  (*       let name = spf "domain_%s" (Nt.layout nt) in *)
  (*       NtMap.add nt (mk_pid name #: (mk_p_set_ty nt))) *)
  (*     types NtMap.empty *)
  (* in *)
  let env =
    {
      gen_ctx = env.gen_ctx;
      recvable_ctx = env.recvable_ctx;
      event_tyctx = ctx_to_map env.event_tyctx;
      p_tyctx;
      (* component_table; *)
      (* sampling_space; *)
    }
  in
  let sampling_types = get_sampling_types env in
  let domain_decls = List.map mk_sample_space_decl sampling_types in
  let entry_args = dest_decl :: domain_decls in
  let entry_input_record = _default_input_name #: (mk_p_record_ty entry_args) in
  let body = compile_term env e #: Nt.Ty_unit in
  let init_stmts =
    List.map
      (fun var ->
        mk_p_assign (mk_pid var, mk_p_field (mk_pid entry_input_record) var.x))
      entry_args
  in
  let func =
    mk_p_function_decl [ entry_input_record ] [] (mk_p_seqs init_stmts body)
  in
  let state = mk_syn_state func in
  let machine = mk_syn_machine state in
  let () =
    Pp.printf "@{<bold>Compile Result:@}:\n%s\n"
      (Toplang.layout_p_machine env 0 machine)
  in
  Toplang.layout_p_machine env 0 machine

(* let compile_term_to_state  *)

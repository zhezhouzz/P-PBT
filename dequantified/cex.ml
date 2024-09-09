open Language
open Zdatatype
open Pfa

let p_option_decl qv =
  (spf "%s_opt" qv.x) #: (mk_p_tuple_ty [ Nt.Ty_bool; qv.ty ])

let p_option_bind decl e1 e2 =
  let is_some, value = mk_depair (mk_pid decl) in
  mk_p_ite is_some (e1 value) e2

let p_option_set_none decl =
  let is_some, _ = mk_depair (mk_pid decl) in
  mk_p_assign (is_some, mk_p_bool false)

let p_option_set_some decl expr =
  let is_some, value = mk_depair (mk_pid decl) in
  let update = mk_p_assign (value, expr) in
  mk_p_ite is_some update
    (Some (mk_p_seq (mk_p_assign (is_some, mk_p_bool true)) update))

let p_option_set_when_none decl expr =
  let is_some, value = mk_depair (mk_pid decl) in
  let update = mk_p_assign (value, expr) in
  mk_p_it (mk_p_not is_some)
    (mk_p_seq (mk_p_assign (is_some, mk_p_bool true)) update)

let cex_name_space qv = (spf "cex_%s" qv.x) #: qv.ty

type cex = {
  total_global_idx : int;
  global_qvs : (Nt.t, string) typed list;
  (* p part *)
  p_global_idx : (Nt.t, string) typed;
  p_state : (Nt.t, string) typed;
  p_cex_init_function : (Nt.t, string) typed;
  p_global_qv : (Nt.t, string) typed -> (Nt.t, string) typed;
  p_check_final_function : (Nt.t, string) typed;
  p_get_available_actions_function : (Nt.t, string) typed;
}

let mk_cex (client : (Nt.t prop * SFA.dfa) list client) =
  (* let pfa = concretlize_atuoamta client.spec_tyctx client.violation in *)
  let global_qvs = get_qvs_from_world client.violation_world in
  let p_state = cex_name_space @@ ("state" #: Nt.Ty_int) in
  let p_global_idx = cex_name_space @@ ("global_idx" #: Nt.Ty_int) in
  let p_cex_init_function = cex_name_space @@ ("init_function" #: Nt.Ty_int) in
  let p_check_final_function = cex_name_space check_final_function_decl in
  let p_get_available_actions_function =
    cex_name_space @@ get_available_actions_function_decl
  in
  let p_global_qv qv = p_option_decl @@ cex_name_space qv in
  {
    total_global_idx = List.length client.violation;
    p_state;
    global_qvs;
    p_global_idx;
    p_global_qv;
    p_cex_init_function;
    p_check_final_function;
    p_get_available_actions_function;
  }

open Register

let mk_cex_check_final_function_decl (cex, pfa) =
  let finals = mk_p_access (mk_pid pfa.p_finals, mk_pid cex.p_global_idx) in
  let res = mk_p_in (mk_pid cex.p_state) finals in
  let body = mk_return res in
  (cex.p_check_final_function, mk_p_function_decl [] [] body)

let mk_p_get_available_actions_function (cex, pfa) =
  let actions = "actions" #: (mk_p_set_ty mk_p_string_ty) in
  let resp_actions = "resp_actions" #: (mk_p_set_ty mk_p_string_ty) in
  let transitions =
    mk_p_access (mk_pid pfa.p_transitions, mk_pid cex.p_global_idx)
  in
  let res = mk_p_map_keys @@ mk_p_access (transitions, mk_pid cex.p_state) in
  let body =
    mk_p_let actions (mk_p_app lib_seq_string_to_set [ res ])
    @@ mk_p_let resp_actions
         (mk_p_app lib_intersection_set
            [ mk_pid p_response_actions_domain; mk_pid actions ])
    @@ (mk_p_it
          (mk_p_not @@ mk_p_app lib_set_is_empty [ mk_pid resp_actions ])
          (mk_p_vassign (actions, mk_pid resp_actions))
       <++> mk_return (mk_pid actions))
  in
  (* let body = mk_return res in *)
  (cex.p_get_available_actions_function, mk_p_function_decl [] [] body)

let register_cex pfa cex m =
  let {
    p_global_idx;
    p_state;
    global_qvs;
    p_global_qv;
    p_cex_init_function;
    total_global_idx;
    _;
  } =
    cex
  in
  let vars = p_global_idx :: p_state :: List.map p_global_qv global_qvs in
  let m = machine_register_local_vars vars m in
  let es =
    [
      mk_p_vassign (p_global_idx, mk_p_choose (mk_p_int total_global_idx));
      mk_p_vassign (p_state, mk_p_int 0);
    ]
    @ List.map (fun qv -> p_option_set_none (p_global_qv qv)) global_qvs
  in
  let decl = (p_cex_init_function, mk_p_function_decl [] [] (mk_p_seqs_ es)) in
  let decl' = mk_cex_check_final_function_decl (cex, pfa) in
  let decl'' = mk_p_get_available_actions_function (cex, pfa) in
  let m = machine_register_local_funcs [ decl; decl'; decl'' ] m in
  m

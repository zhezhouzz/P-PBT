open Language

let machine_register_local_funcs funcs m =
  { m with local_funcs = m.local_funcs @ funcs }

let machine_register_local_vars vars m =
  { m with local_vars = m.local_vars @ vars }

let init_state func =
  {
    name = init_state_name;
    state_label = [ Start ];
    state_body = [ (Entry #: Nt.Ty_unit, func) ];
  }

let loop_state funcs =
  { name = loop_state_name; state_label = []; state_body = funcs }

let err_state funcs =
  { name = error_state_name; state_label = []; state_body = funcs }

let machine_register_init_state_with_func func m =
  { m with states = m.states @ [ init_state func ] }

let machine_register_loop_state_with_funcs func m =
  { m with states = m.states @ [ loop_state func ] }

let machine_register_err_state_with_funcs func m =
  { m with states = m.states @ [ err_state func ] }

let machine_register_operation (vars, funcs) m =
  let m = machine_register_local_vars vars m in
  let m = machine_register_local_funcs funcs m in
  m

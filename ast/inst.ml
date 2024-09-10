open Sexplib.Std
open Zutils
open Zdatatype

type world =
  | WState (* always int *)
  | WSingle of { qv : (Nt.t, string) typed; world : world }
  | WMap of { qv : (Nt.t, string) typed; world : world }

type 'a client = {
  spec_tyctx : Item.spec_tyctx;
  client_name : string;
  event_scope : string list;
  type_configs : string list;
  axiom_world : world;
  axiom : 'a;
  violation_world : world;
  violation : 'a;
  step_bound : int;
}

let mk_forall_world =
  let rec aux = function
    | [] -> WState
    | qv :: t -> WMap { qv; world = aux t }
  in
  aux

let mk_exists_world =
  let rec aux = function
    | [] -> WState
    | qv :: t -> WSingle { qv; world = aux t }
  in
  aux

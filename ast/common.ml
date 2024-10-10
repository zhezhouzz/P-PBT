let v_name = "v"
let v_ret_name = "vret"

open Zutils
include Prop

let str_eq_to_bv y x = match x with Some x -> String.equal x y | None -> false
(* let vs_names n = List.init n (fun i -> spf "%s%i" "x_" i) *)

let _get_record_ty_fields loc ty =
  match ty with Nt.Ty_record l -> l | _ -> _failatwith loc "die"

let rename_qv x = (Rename.unique x.x) #: x.ty
let name_in_qvs name l = List.exists (fun x -> String.equal x.x name) l

(* let vs_names_from_types tps = *)
(*   let n = List.length tps in *)
(*   let vs = vs_names n in *)
(*   List.map (fun (x, ty) -> x #: ty) @@ _safe_combine [%here] vs tps *)

(* for automata *)
(* type state = int *)

(* let _default_init_state = 0 *)

(* module StateSet = Set.Make (Int) *)
(* module StateMap = Map.Make (Int) *)

(* module type CHARAC = sig *)
(*   include Map.OrderedType *)

(*   val layout : t -> string *)
(*   val delimit_cotexnt_char : t list option * t -> t list *)
(* end *)

(* module type CHARACTER = sig *)
(*   include CHARAC *)

(*   type char_idx *)

(*   val layout : t -> string *)
(*   val init_char_map : unit -> char_idx *)
(*   val add_char_to_map : char_idx -> t -> unit *)
(*   val id2c : char_idx -> Int64.t -> t *)
(*   val c2id : char_idx -> t -> Int64.t *)
(* end *)

let mk_p_abstract_ty name = Nt.Ty_constructor (name, [])
let mk_p_set_ty ty = Nt.Ty_constructor ("set", [ ty ])
let mk_p_seq_ty ty = Nt.Ty_constructor ("seq", [ ty ])
let mk_p_map_ty ty1 ty2 = Nt.Ty_constructor ("map", [ ty1; ty2 ])
let mk_p_event_ty = mk_p_abstract_ty "event"
let mk_p_ref_ty ty = Nt.Ty_constructor ("ref", [ ty ])
let mk_p_record_ty vs = Nt.Ty_record vs
let mk_p_string_ty = mk_p_abstract_ty "string"
let mk_p_regex_ty = mk_p_abstract_ty "regex"

let is_p_abstact_ty name = function
  | Nt.Ty_constructor (name', []) when String.equal name name' -> true
  | _ -> false

let mk_p_tuple_ty vs =
  Nt.Ty_record (List.mapi (fun i ty -> (string_of_int i) #: ty) vs)

let mk_p_machine_ty = mk_p_abstract_ty "machine"
let is_empty_record_ty = function Nt.Ty_record [] -> true | _ -> false

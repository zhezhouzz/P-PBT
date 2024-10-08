open Sexplib.Std
open Prop
open Zutils
open Common

type 't sevent =
  | GuardEvent of { vs : ('t, string) typed list; phi : 't prop }
  | EffEvent of { op : string; vs : ('t, string) typed list; phi : 't prop }
[@@deriving sexp, show, eq, ord]

(* let vs_names_from_types tps = *)
(*   let n = List.length tps in *)
(*   let vs = vs_names n in *)
(*   List.map (fun (x, ty) -> x #: ty) @@ _safe_combine [%here] vs tps *)

(* let __server_feild = "dest" *)
(* let server_type = Nt.Ty_constructor ("server", []) *)

let _get_sevent_fields location = function
  | EffEvent { op; vs; phi } -> (op, vs, phi)
  | GuardEvent _ -> _die location

let _get_sevent_name location p =
  let res, _, _ = _get_sevent_fields location p in
  res

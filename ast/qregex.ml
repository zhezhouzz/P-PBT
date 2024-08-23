open Common
open Mtyped
open Regex
open Sexplib.Std
open Sugar

type ('t, 'a) qregex =
  | Regex of 'a regex
  | RPi of { sort : ('t, string) typed; [@bound] body : ('t, 'a) qregex }
  | RForall of { qv : (('t, string) typed[@bound]); body : ('t, 'a) qregex }
  | RExists of { qv : (('t, string) typed[@bound]); body : ('t, 'a) qregex }
[@@deriving sexp]

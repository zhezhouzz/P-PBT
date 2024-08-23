include Syntax
include Common
include To_constant
include To_id
include To_lit
include To_sevent
include To_prop
include To_regex

(* include To_inst *)
include To_item

(* module Nt = struct *)
(*   include Nt.T *)
(*   include Nt *)
(* end *)

let layout_str_regex regex = To_regex.layout Nt.layout (fun x -> x) regex

let layout_symbolic_regex regex =
  To_regex.layout Nt.layout To_sevent.layout regex

let layout_desym_regex regex = To_regex.layout Nt.layout DesymLabel.layout regex

let layout_ntopt_symbolic_regex expr =
  To_regex.layout Ntopt.layout To_sevent.layout expr

let str_regex_of_expr = To_regex.of_expr id_of_expr
let symbolic_regex_of_expr = To_regex.of_expr To_sevent.of_expr

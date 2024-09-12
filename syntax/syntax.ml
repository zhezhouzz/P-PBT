include Common

(* include Typectx *)
(* include Regex *)
include Pmachine

(* include Qregex *)
(* include Nfa *)
include Item
include Inst

(* include Minterm *)
(* include FiniteAutomata *)
include Backend
include Wrapper
include Ast

(* let _tmp_dot_path = ".tmp.dot" *)

(* module MakeA (C : CHARAC) = struct *)
(*   module Tmp = MakeAutomata (MakeC (C)) *)
(*   include MakeAutomataDot (Tmp) *)
(*   include Tmp *)
(* end *)

(* module MakeAA (C : CHARAC) = struct *)
(*   include MakeA (C) *)

(*   let index_regex (regex : ('t, C.t) regex) : C.char_idx = *)
(*     let m = C.init_char_map () in *)
(*     let () = iter_label_in_regex (C.add_char_to_map m) regex in *)
(*     m *)

(*   let to_index_regex (m : C.char_idx) (regex : ('t, C.t) regex) : *)
(*       ('t, Int64.t) regex = *)
(*     map_label_in_regex (C.c2id m) regex *)

(*   let from_index_regex (m : C.char_idx) (regex : ('t, Int64.t) regex) : *)
(*       ('t, C.t) regex = *)
(*     map_label_in_regex (C.id2c m) regex *)

(*   open Core *)

(*   let save_dfa_as_digraph sfa filename = *)
(*     Format.fprintf *)
(*       (Format.formatter_of_out_channel @@ Out_channel.create filename) *)
(*       "%a@." format_digraph *)
(*       (digraph_of_nfa (force_nfa sfa)) *)

(*   let display_dfa sfa = *)
(*     let () = save_dfa_as_digraph sfa _tmp_dot_path in *)
(*     let () = Out_channel.(flush stdout) in *)
(*     (\* let () = UnixLabels.sleep 1 in *\) *)
(*     (\* let ch = Core_unix.open_process_out "ls" in *\) *)
(*     (\* Core_unix.(close_process_out ch) *\) *)
(*     Core_unix.( *)
(*       close_process_out @@ open_process_out *)
(*       @@ spf "cat %s | dot -Tpng | imgcat" _tmp_dot_path) *)
(* end *)

(* module CharC = struct *)
(*   include Char *)

(*   let layout x = spf "%c" x *)
(*   let delimit_cotexnt_char (_, c) = [ c ] *)
(* end *)

(* module StringC = struct *)
(*   include String *)

(*   let layout x = x *)
(*   let delimit_cotexnt_char (_, c) = [ c ] *)
(* end *)

(* module Int64C = struct *)
(*   include Int64 *)

(*   let layout = to_string *)
(*   let delimit_cotexnt_char (_, c) = [ c ] *)
(* end *)

(* module DesymLabel = struct *)
(*   type t = string * int *)

(*   let compare (a : t) (b : t) = Stdlib.compare a b *)
(*   let layout (op, id) = op ^ ":" ^ string_of_int id *)
(*   let delimit_cotexnt_char (_, c) = [ c ] *)
(*   let eq (s1, i1) (s2, i2) = String.equal s1 s2 && Int.equal i1 i2 *)
(* end *)

(* module CharAutomata = MakeAA (CharC) *)
(* module StrAutomata = MakeAA (StringC) *)
(* module IdAutomata = MakeAA (Int64C) *)
(* module DesymFA = MakeAA (DesymLabel) *)

open Ocaml5_parser
open Mutils
open Mtyped
open Parsetree
module Nt = Normalty.Frontend

let mk_app_expr func args =
  let args = List.map (fun x -> (Asttypes.Nolabel, x)) args in
  desc_to_ocamlexpr @@ Pexp_apply (func, args)

let mk_tuple_expr es = desc_to_ocamlexpr @@ Pexp_tuple es

let typed_to_expr f expr =
  match expr.ty with
  | None -> f expr.x
  | Some ty ->
      desc_to_ocamlexpr @@ Pexp_constraint (f expr.x, Nt.t_to_core_type ty)

let update_ty { x; ty } ty' =
  match ty with None -> x #: (Some ty') | Some _ -> x #: (Some ty')

let notated (name, t) =
  desc_to_ct
  @@ Ptyp_extension (Location.mknoloc name, PTyp (Nt.t_to_core_type t))

let quantifier_to_pattern (q, u) =
  dest_to_pat
    (Ppat_constraint
       ( dest_to_pat (Ppat_var (Location.mknoloc u.x)),
         notated (Normalty.Connective.qt_to_string q, u.ty) ))

open Sugar

let smt_layout_ty = function
  | Some Nt.T.Ty_bool -> "Bool"
  | Some Nt.T.Ty_int -> "Int"
  | Some (Nt.T.Ty_constructor _) -> "Int"
  | _ -> _failatwith __FILE__ __LINE__ "unimp"

type 't layout_setting = {
  sym_true : string;
  sym_false : string;
  sym_and : string;
  sym_or : string;
  sym_not : string;
  sym_implies : string;
  sym_iff : string;
  sym_forall : string;
  sym_exists : string;
  layout_typedid : ('t, string) typed -> string;
  layout_mp : string -> string;
}

let detailssetting =
  {
    sym_true = "⊤";
    sym_false = "⊥";
    sym_and = " ∧ ";
    sym_or = " ∨ ";
    sym_not = "¬";
    sym_implies = "=>";
    sym_iff = "<=>";
    sym_forall = "∀";
    sym_exists = "∃";
    layout_typedid = Nt.(fun x -> spf "(%s:%s)" x.x (layout x.ty));
    layout_mp = (fun x -> x);
  }

let psetting =
  {
    sym_true = "⊤";
    sym_false = "⊥";
    sym_and = " ∧ ";
    sym_or = " ∨ ";
    sym_not = "¬";
    sym_implies = "=>";
    sym_iff = "<=>";
    sym_forall = "∀";
    sym_exists = "∃";
    layout_typedid = (fun x -> x.x);
    (* (fun x ->          Printf.spf "(%s:%s)" x.x (Ty.layout x.ty)); *)
    layout_mp = (fun x -> x);
  }

let rawsetting =
  {
    sym_true = "true";
    sym_false = "false";
    sym_and = " && ";
    sym_or = " || ";
    sym_not = "~";
    sym_implies = "=>";
    sym_iff = "<=>";
    sym_forall = "∀";
    sym_exists = "∃";
    layout_typedid = (fun x -> x.x);
    (* (fun x ->          Printf.spf "(%s:%s)" x.x (Ty.layout x.ty)); *)
    layout_mp = (fun x -> x);
  }

let coqsetting =
  {
    sym_true = "True";
    sym_false = "False";
    sym_and = " /\\ ";
    sym_or = " \\/ ";
    sym_not = "~";
    sym_implies = "->";
    sym_iff = "<->";
    sym_forall = "forall ";
    sym_exists = "exists ";
    layout_typedid = (fun x -> x.x);
    layout_mp = (function "==" -> "=" | x -> x);
  }

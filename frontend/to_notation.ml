open Ocaml5_parser
open Parsetree
open Sugar
open Mtyped

let get_denoteopt_from_attr a =
  match a with [ x ] -> Some x.attr_name.txt | _ -> None

let get_denoteopt expr = get_denoteopt_from_attr expr.pexp_attributes

let get_denote expr =
  match get_denoteopt expr with
  | Some x -> x
  | None -> _failatwith __FILE__ __LINE__ ""

let get_pat_denoteopt pat = get_denoteopt_from_attr pat.ppat_attributes

let get_pat_denote expr =
  match get_pat_denoteopt expr with
  | Some x -> x
  | None -> _failatwith __FILE__ __LINE__ ""

type notation = FA | EX | PI

let layout_notation = function FA -> "forall" | EX -> "exist" | PI -> "pi"

let quantifier_of_notation = function
  | FA -> Normalty.Connective.Fa
  | EX -> Normalty.Connective.Ex
  | PI -> _die [%here]

let pi_of_notation = function PI -> true | _ -> false

let notation_of_expr arg =
  match arg.ppat_desc with
  | Ppat_constraint (arg, ct) ->
      let q =
        match get_pat_denoteopt arg with
        | None -> FA
        (* here we assume it has forall by default. *)
        | Some "forall" -> FA
        | Some "exists" -> EX
        | Some "pi" -> PI
        | Some _ ->
            _failatwith __FILE__ __LINE__
              "quantifier needs be [@forall] or [@exists]"
        (* | Some q -> Normalty.Connective.qt_of_string q *)
      in
      let arg =
        match arg.ppat_desc with
        | Ppat_var arg -> arg.txt
        | _ -> failwith "parsing: prop function"
      in
      let ty = Normalty.Frontend.core_type_to_t ct in
      (q, arg #: (Some ty))
  | _ -> _failatwith __FILE__ __LINE__ "quantifier needs type notation"

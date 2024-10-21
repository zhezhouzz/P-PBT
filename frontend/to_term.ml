open Ast
open Zdatatype

let layout_value = function VVar x -> x.x | VConst c -> layout_constant c
let layout_typed_value v = layout_value v.x

let rec layout_term = function
  | CVal v -> layout_typed_value v
  | CLetE { lhs = []; rhs; body } ->
      spf "%s; %s" (layout_term rhs.x) (layout_term body.x)
  | CLetE { lhs; rhs; body } ->
      spf "let (%s) = %s in %s"
        (List.split_by_comma _get_x lhs)
        (layout_term rhs.x) (layout_term body.x)
  | CAppOp { op; args } ->
      spf "%s %s" op.x (List.split_by " " layout_typed_value args)
  | CObs { op; prop } -> spf "obs %s; assert %s" op.x (layout_prop prop)
  | CGen { op; args } ->
      spf "gen %s(%s)" op.x (List.split_by " " layout_typed_value args)
  | CUnion es -> List.split_by " ⊕\n" layout_term es
  | CAssert v -> spf "assert %s" (layout_value v)
  (* | CRandom nt -> spf "random %s" @@ Nt.layout nt *)
  | CAssume (nt, phi) ->
      spf "assume[%s] %s" (Nt.layout (Ty_tuple nt)) (layout_prop phi)
  | CAssertP phi -> spf "assert %s" (layout_prop phi)
(* spf "assert %s" (show_prop phi) *)

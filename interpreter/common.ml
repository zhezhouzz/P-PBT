open Language
open Zdatatype

let choose_from_list l = List.nth l @@ Random.int (List.length l)

let eval_qv store x =
  match StrMap.find_opt store x.x with Some c -> c | None -> _die [%here]

let eval_value store = function VVar x -> eval_qv store x | VConst c -> c
let meval_value store values = List.map (fun v -> eval_value store v.x) values
let const_to_bool loc = function B b -> b | _ -> _die_with loc "never"

let eval_app_op op cs =
  match (op.x, cs) with
  | "==", [ a; b ] -> B (equal_constant a b)
  | ">", [ I a; I b ] -> B (a > b)
  | _ -> _die_with [%here] "unimp"

let eval_lit store lit =
  let rec aux lit =
    match lit with
    | AC c -> c
    | AAppOp (op, args) -> eval_app_op op @@ List.map (fun l -> aux l.x) args
    | ATu _ | AProj _ -> _die_with [%here] "never"
    | AVar x -> eval_qv store x
  in
  aux lit

let eval_prop store prop =
  let rec aux = function
    | Lit lit -> const_to_bool [%here] @@ eval_lit store lit.x
    | Implies (p1, p2) -> if aux p1 then aux p2 else true
    | And ps -> List.fold_left (fun res p -> res && aux p) true ps
    | Or ps -> List.fold_left (fun res p -> res || aux p) false ps
    | Not p -> not (aux p)
    | Iff (p1, p2) -> aux p1 == aux p2
    | Ite (p1, p2, p3) -> if aux p1 then aux p2 else aux p3
    | Forall _ | Exists _ -> _die_with [%here] "never"
  in
  aux prop

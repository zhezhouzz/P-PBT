let rec is_p_prim_type = function
  | Nt.Ty_bool | Nt.Ty_int -> true
  | Nt.Ty_record l -> List.for_all (fun (_, ty) -> is_p_prim_type ty) l
  | Nt.Ty_tuple l -> List.for_all is_p_prim_type l
  | Nt.Ty_constructor (name, []) when String.equal name "machine" -> true
  | Nt.Ty_constructor (name, [ nt ]) ->
      (String.equal "set" name || String.equal "req" name) && is_p_prim_type nt
  | Nt.Ty_constructor (name, [ nt1; nt2 ]) ->
      String.equal "map" name && is_p_prim_type nt1 && is_p_prim_type nt2
  | _ -> false

open Ast
open Zzdatatype.Datatype

let get_absty nt =
  let rec aux = function
    | Nt.Ty_bool | Nt.Ty_int -> []
    | Nt.Ty_record l -> List.concat_map (fun (_, ty) -> aux ty) l
    | Nt.Ty_tuple l -> List.concat_map aux l
    | Nt.Ty_constructor (name, []) when String.equal name "machine" -> []
    | Nt.Ty_constructor (name, []) -> [ name ]
    | Nt.Ty_constructor (_, [ nt ]) -> aux nt
    | Nt.Ty_constructor (_, [ nt1; nt2 ]) -> aux nt1 @ aux nt2
    | _ -> _die [%here]
  in
  List.slow_rm_dup String.equal (aux nt)

type result = EnumType of string | Dependent of string list | NType of Nt.t

let get_type_from_wrapper_opt name code =
  let res =
    List.filter_map
      (function
        | WrapperEnum { enum_name; _ } when String.equal enum_name name ->
            Some (mk_p_abstract_ty enum_name, [])
        | WrapperTypeAlias { type_name; alias_type }
          when String.equal type_name name ->
            Some (alias_type, get_absty alias_type)
        | WrapperEventDecl { event_name; event_type }
          when String.equal event_name name ->
            Some (event_type, get_absty event_type)
        | WrapperMachineDecl { machine_name; _ }
          when String.equal machine_name name ->
            Some (mk_p_machine_ty, [])
        | WrapperSpecEventDecl { event_name; spec_event_type; p_event_name; _ }
          when String.equal event_name name ->
            Some (spec_event_type, [ p_event_name ])
        | _ -> None)
      code
  in
  match res with
  | [] -> _die_with [%here] (spf "cannot find %s" name)
  | [ res ] -> res
  | l ->
      let () =
        Printf.printf "multiple: %s\n"
          (List.split_by_comma (fun (nt, _) -> Nt.layout nt) l)
      in
      _die [%here]

let filter_wrapper f code =
  let aux = function
    | WrapperEnum { enum_name; _ } -> f enum_name
    | WrapperTypeAlias { type_name; _ } -> f type_name
    | WrapperEventDecl { event_name; _ } -> f event_name
    | WrapperMachineDecl { machine_name; _ } -> f machine_name
    | WrapperSpecEventDecl _ -> true
    | Dummy -> false
  in
  List.filter aux code

let simplify_wrapper (code : p_wrapper list) names =
  let rec aux (env : Nt.t StrMap.t) (fv : string list) =
    match fv with
    | [] -> env
    | name :: fv ->
        if StrMap.mem name env then aux env fv
        else
          let nt, fv' = get_type_from_wrapper_opt name code in
          let env = StrMap.add name nt env in
          aux env (fv' @ fv)
  in
  let env = aux StrMap.empty names in
  let names = StrMap.to_key_list env in
  (env, filter_wrapper (fun name -> List.exists (String.equal name) names) code)

open Syntax
open P_machine_typing
open P_func_typing
open Zzdatatype.Datatype

let p_items_infer (ctx : t ctx) l =
  let prim_func_decl =
    List.filter_map
      (function
        | PPrimFuncDecl fname -> Some (__force_typed __FILE__ __LINE__ fname)
        | _ -> None)
      l
  in
  (* let () = *)
  (*   Printf.printf "%s\n" @@ List.split_by_comma (fun x -> x.x) prim_func_decl *)
  (* in *)
  let ctx = add_to_rights ctx prim_func_decl in
  let global_funcs =
    List.filter_map
      (function PGlobalFunc (fname, f) -> Some (fname, f) | _ -> None)
      l
  in
  let ctx = add_to_rights ctx (try_func_typing global_funcs) in
  let _, l =
    List.fold_left
      (fun (ctx, fs) -> function
        | PEnumDecl (name, ns) -> (ctx, fs @ [ PEnumDecl (name, ns) ])
        | PTypeDecl x -> (ctx, fs @ [ PTypeDecl x ])
        | PEventDecl x -> (ctx, fs @ [ PEventDecl x ])
        | PPrimFuncDecl fname ->
            (ctx, fs @ [ PPrimFuncDecl (__force_typed __FILE__ __LINE__ fname) ])
        | PGlobalFunc (fname, f) ->
            let ctx, (fname, f) = func_infer_add_to_ctx ctx (fname, f) in
            (ctx, fs @ [ PGlobalFunc (fname, f) ])
        | PMachine m ->
            let m = machine_infer ctx m in
            (ctx, fs @ [ PMachine m ]))
      (ctx, []) l
  in
  l

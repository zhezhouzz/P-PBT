open Ast
open Zdatatype

let mt_to_string { op; global_embedding; local_embedding } =
  spf "%s_%i_%i" op global_embedding local_embedding

let string_to_mt str =
  match
    List.filter (fun l -> String.length l > 0) @@ String.split_on_char '_' str
  with
  | [ op; global_embedding; local_embedding ] ->
      let global_embedding, local_embedding =
        map2 int_of_string (global_embedding, local_embedding)
      in
      { op; global_embedding; local_embedding }
  | _ -> _die_with [%here] (spf "string_to_mt: %s" str)

let mts_fold_on_op op f (i_s_il : mts) res =
  IntMap.fold
    (fun global_embedding s_il res ->
      match StrMap.find_opt s_il op with
      | None -> res
      | Some il ->
          List.fold_right
            (fun local_embedding res ->
              f { global_embedding; op; local_embedding } res)
            il res)
    i_s_il res

let mts_local_fold_on_op global_embedding op f (i_s_il : mts) res =
  let s_il = IntMap.find "err" i_s_il global_embedding in
  match StrMap.find_opt s_il op with
  | None -> res
  | Some il ->
      List.fold_right
        (fun local_embedding res ->
          f { global_embedding; op; local_embedding } res)
        il res

let mts_fold f (i_s_il : mts) res =
  IntMap.fold
    (fun global_embedding s_il res ->
      StrMap.fold
        (fun op il res ->
          List.fold_right
            (fun local_embedding res ->
              f { global_embedding; op; local_embedding } res)
            il res)
        s_il res)
    i_s_il res

let mts_local_fold global_embedding f (i_s_il : mts) res =
  let s_il = IntMap.find "err" i_s_il global_embedding in
  StrMap.fold
    (fun op il res ->
      List.fold_right
        (fun local_embedding res ->
          f { global_embedding; op; local_embedding } res)
        il res)
    s_il res

let mts_map f (i_s_il : mts) =
  IntMap.mapi
    (fun global_embedding s_il ->
      StrMap.mapi
        (fun op il ->
          List.map
            (fun local_embedding -> f { global_embedding; op; local_embedding })
            il)
        s_il)
    i_s_il

let mts_filter_map f (i_s_il : mts) =
  IntMap.filter_map
    (fun global_embedding s_il ->
      let s_il =
        StrMap.filter_map
          (fun op il ->
            let il =
              List.filter_map
                (fun local_embedding ->
                  f { global_embedding; op; local_embedding })
                il
            in
            if List.length il == 0 then None else Some il)
          s_il
      in
      if StrMap.cardinal s_il == 0 then None else Some s_il)
    i_s_il

let s_il_is_empty s_il =
  StrMap.exists (fun _ l -> match l with [] -> true | _ -> false) s_il

let mts_to_global_m i_s_il =
  IntMap.to_key_list @@ IntMap.map (fun m -> not (s_il_is_empty m)) i_s_il

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
      let b = pow a (n / 2) in
      b * b * if n mod 2 = 0 then 1 else a

let rec id_to_bl len n res =
  if len == 0 then res
  else
    let x = 0 == n mod 2 in
    id_to_bl (len - 1) (n / 2) (x :: res)

let pprint_bl bl = List.split_by "" (fun b -> if b then "1" else "0") bl

let pprint_mts =
  IntMap.iter (fun global_embedding s_il ->
      let () = Pp.printf "[global %i]\n" global_embedding in
      let () =
        StrMap.iter
          (fun op l ->
            let () = Pp.printf "\t[op %s]: " op in
            Pp.printf "%s\n" @@ List.split_by "," string_of_int l)
          s_il
      in
      ())

let id_to_barr len n = Array.of_list @@ id_to_bl len n []

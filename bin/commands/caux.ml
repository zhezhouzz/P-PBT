open Core

let regular_file =
  Command.Arg_type.create (fun filename ->
      match Sys_unix.is_file filename with
      | `Yes -> filename
      | `No -> failwith "Not a regular file"
      | `Unknown -> failwith "Could not determine if this was a regular file")

(** [dir_is_empty dir] is true, if [dir] contains no files except
 * "." and ".."
*)
let dir_is_empty dir = Array.length (Sys_unix.readdir dir) = 0

(** [dir_contents] returns the paths of all regular files that are
 * contained in [dir]. Each file is a path starting with [dir].
*)
let dir_contents dir =
  let rec loop result = function
    | f :: fs -> (
        match Sys_unix.is_directory f with
        | `Yes ->
            Sys_unix.readdir f |> Array.to_list
            |> List.map ~f:(Filename.concat f)
            |> List.append fs |> loop result
        | _ -> loop (f :: result) fs)
    | [] -> result
  in
  loop [] [ dir ]

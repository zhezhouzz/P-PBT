(* open Common *)
open Sugar

type 'a state = { is_terminal : bool; is_open : bool; s : 'a }
type ('a, 'b) path = ('a state * 'b) list * 'a state

type ('a, 'b) path_tree =
  | PathLeaf of 'a state
  | PathNode of { parent : 'a state; children : ('b * ('a, 'b) path_tree) list }

let mk_state s is_terminal is_open = { s; is_open; is_terminal }
let get_root = function PathLeaf en -> en | PathNode { parent; _ } -> parent

let rec num_pnode = function
  | PathLeaf _ -> 1
  | PathNode { children; _ } ->
      List.fold_left ( + ) 1 (List.map num_pnode#.snd children)

let modify_by_children
    (f : 'a state -> ('b * ('a, 'b) path_tree) list -> ('a, 'b) path_tree)
    (tr : ('a, 'b) path_tree) =
  let rec dfs tr =
    match tr with
    | PathLeaf _ -> tr
    | PathNode { parent; children } ->
        let children = List.map (fun (ch, tr') -> (ch, dfs tr')) children in
        f parent children
  in
  dfs tr

let modify (f : ('a, 'b) path -> ('a, 'b) path_tree option)
    (tr : ('a, 'b) path_tree) =
  let rec dfs prefix tr =
    let tr =
      match f (prefix, get_root tr) with None -> tr | Some tr' -> tr'
    in
    match tr with
    | PathLeaf _ -> tr
    | PathNode { parent; children } ->
        let children =
          List.map
            (fun (ch, tr') -> (ch, dfs (prefix @ [ (parent, ch) ]) tr'))
            children
        in
        PathNode { parent; children }
  in
  dfs [] tr

let set_close (f : ('a, 'b) path -> bool option) (tr : ('a, 'b) path_tree) =
  modify
    (fun (prefix, en) ->
      let* is_open = f (prefix, en) in
      Some (PathLeaf { en with is_open }))
    tr

let prune_by_length (n : int) (tr : ('a, 'b) path_tree) =
  modify
    (fun (prefix, en) ->
      if List.length prefix < n then None
      else Some (PathLeaf { en with is_open = false }))
    tr

let rec ptree_has_terminal = function
  | PathLeaf s -> s.is_terminal
  | PathNode { parent; children } ->
      parent.is_terminal || pchildren_has_terminal children

and pchildren_has_terminal l =
  List.exists (fun (_, tr) -> ptree_has_terminal tr) l

let prune_non_terminal (tr : ('a, 'b) path_tree) =
  modify_by_children
    (fun parent children ->
      let children = List.filter ptree_has_terminal#.snd children in
      match children with
      | [] -> PathLeaf parent
      | _ -> PathNode { parent; children })
    tr

let modify_leaf (f : ('a, 'b) path -> ('a, 'b) path_tree option)
    (tr : ('a, 'b) path_tree) =
  let rec dfs prefix tr =
    match tr with
    | PathLeaf state -> (
        match f (prefix, state) with None -> tr | Some tr' -> tr')
    | PathNode { parent; children } ->
        let children =
          List.map
            (fun (ch, tr') -> (ch, dfs (prefix @ [ (parent, ch) ]) tr'))
            children
        in
        PathNode { parent; children }
  in
  dfs [] tr

let iter_terminate_path (f : ('a, 'b) path -> unit) (tr : ('a, 'b) path_tree) =
  let rec dfs prefix tr =
    match tr with
    | PathLeaf state -> if state.is_terminal then f (prefix, state) else ()
    | PathNode { parent; children } ->
        let () = if parent.is_terminal then f (prefix, parent) else () in
        List.iter
          (fun (ch, tr') -> dfs (prefix @ [ (parent, ch) ]) tr')
          children
  in
  dfs [] tr

let fold_terminate_path (f : ('a, 'b) path -> 'c -> 'c)
    (tr : ('a, 'b) path_tree) (init : 'c) =
  let res = ref init in
  let f p = res := f p !res in
  iter_terminate_path f tr;
  !res

let to_path_list (tr : ('a, 'b) path_tree) =
  fold_terminate_path (fun p res -> p :: res) tr []

let to_chpath_list (tr : ('a, 'b) path_tree) =
  List.map (fun (prefix, _) -> List.map snd prefix) @@ to_path_list tr

let append (f : 'a state -> ('b * 'a state) list) (tr : ('a, 'b) path_tree) =
  modify_leaf
    (fun (_, parent) ->
      match f parent with
      | [] -> None
      | l ->
          let children = List.map (fun (ch, dest) -> (ch, PathLeaf dest)) l in
          Some (PathNode { parent; children }))
    tr

let rename_states ptree =
  let rec dfs (s, tr) =
    match tr with
    | PathLeaf { is_terminal; is_open; _ } ->
        (s + 1, PathLeaf { is_terminal; is_open; s })
    | PathNode { parent; children } ->
        let parent = { parent with s } in
        let s, children =
          List.fold_right
            (fun (ch, tr) (s, res) ->
              let s, tr = dfs (s, tr) in
              (s + 1, (ch, tr) :: res))
            children
            (s + 1, [])
        in
        (s, PathNode { parent; children })
  in
  snd (dfs (0, ptree))

let get_transitions ptree =
  let rec dfs tr =
    match tr with
    | PathLeaf _ -> []
    | PathNode { parent; children } ->
        List.fold_right
          (fun (ch, tr) res -> ((parent, ch, get_root tr) :: dfs tr) @ res)
          children []
  in
  dfs ptree

let get_terminals ptree =
  let rec dfs tr =
    match tr with
    | PathLeaf s -> if s.is_terminal then [ s.s ] else []
    | PathNode { parent; children } ->
        let res = if parent.is_terminal then [ parent.s ] else [] in
        List.fold_right (fun (_, tr) res -> dfs tr @ res) children res
  in
  dfs ptree

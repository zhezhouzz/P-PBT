open AutomataLibrary
open SFA

let rec nullable (r : raw_regex) =
  match r with
  | Empty -> false
  | Eps -> true
  | MultiChar _ -> false
  | Seq l -> List.for_all nullable l
  | Inters (r1, r2) -> nullable r1 && nullable r2
  | Alt (r1, r2) -> nullable r1 || nullable r2
  | Comple (_, r) -> not (nullable r)
  | Star _ -> true

let brzozowski_derivative_char (f : 'a -> C.t -> bool) (char : 'a)
    (r : raw_regex) =
  let rec aux = function
    | Empty -> Empty
    | Eps -> Empty
    | MultiChar cs -> if CharSet.exists (f char) cs then Eps else Empty
    | Seq l ->
        let rec iter res = function
          | [] -> res
          | r :: l ->
              let res = seq (aux r :: l) :: res in
              if nullable r then iter res l else res
        in
        alt_list (iter [] l)
    | Inters (r1, r2) -> Inters (aux r1, aux r2)
    | Alt (r1, r2) -> Alt (aux r1, aux r2)
    | Comple (cs, r) -> Comple (cs, aux r)
    | Star r -> seq [ aux r; Star r ]
  in
  aux r

let brzozowski_derivative (f : 'a -> C.t -> bool) (r : raw_regex) l =
  let rec aux r = function
    | [] -> r
    | u :: l -> aux (brzozowski_derivative_char f u r) l
  in
  aux r l

let is_match (f : 'a -> C.t -> bool) (r : raw_regex) l =
  nullable (brzozowski_derivative f r l)

(* let reduce_sevent (op, cs) = function *)
(*   | Effect  *)

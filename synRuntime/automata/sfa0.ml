val ( == ) : 'a -> 'a -> bool
val ( != ) : 'a -> 'a -> bool

type server = int
type valDom = int

val write : < key : valDom >
val read : < v : valDom >

(* let[@sregex] poly_spec ((n [@forall]) : int) ((server [@pi]) : int) *)
(*     ((valDom [@pi]) : int) ((server [@forall]) : server) *)
(*     ((y [@forall]) : valDom) = *)
(*   ctxOp [| read; write |] *)
(*     (starA (Write (s, x, s == server && x != y)); *)
(*      repeat n anyA; *)
(*      starA (Write (s, x, s == server && x == y))) *)

let[@machine] specA ((n [@forall]) : int) ((server [@forall]) : server)
    ((y [@forall]) : valDom) =
  ctxOp [| read; write |]
    (starA (Write (x, dest == server && x != y));
     repeat n anyA;
     starA (Write (x, dest == server && x == y)))

let[@typedef] serverType = [| 1; 2 |]
let[@typedef] valueType = [| 1; 2; 3 |]

let[@machine] client =
  let server = serverType in
  let valDom = valueType in
  specA 3

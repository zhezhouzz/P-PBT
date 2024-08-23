val "==" : 'a -> 'a -> bool;
val "!=" : 'a -> 'a -> bool;

type server <: int;
type key <: int;

event write : <dest : server ; k : key; value: int>;
event read : <dest : server; k : key >;

machine w1 = forall (s: server), forall (y: key),
   <[function
     | write -> dest == s && k == y
     | read -> dest == s]>;

machine prop = forall (n: int), forall (serv : server), forall (y:key),
 ctx [| read write |]
   (((w1 serv y)*)~(rep n .)~(<[ write s x value |s == serv && x == y ]>*));

const serverType = [|1; 2|];
const valueType = [|1; 2; 3|];

machine client =
   let server = serverType in
   let key = valueType in
   prop 3

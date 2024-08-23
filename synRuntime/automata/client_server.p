val "==" : 'a -> 'a -> bool;
val "!=" : 'a -> 'a -> bool;

type server <: int;
type key <: int;

request event writeReq : <k : key; value: int>;
request event readReq : <k : key >;
response event writeResp : <k : key; value: int>;
response event readResp : <k : key; value: int>;

machine w1 (s: server) (y: key) =
   <[function
     | writeReq -> k == y
     | all -> dest == s]>;

machine prop =
   forall (serv : server), forall (y: key),
   ctx [| readReq writeReq readResp writeResp |]
   (.* ~ (w1 serv y) ~ .*);

const serverType = [|1; 2|];
const valueType = [|1; 2; 3|];

machine client =
   let server = serverType in
   let key = valueType in
   prop

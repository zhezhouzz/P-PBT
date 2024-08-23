val "==" : 'a -> 'a -> bool;
val "!=" : 'a -> 'a -> bool;
type server <: int;
type key <: int;

event write: <dest : server ; k : key; value: int >;
event read :<dest : server; k : key >;
const serverType =[|1; 2|]

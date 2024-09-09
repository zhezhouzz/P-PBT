type 't ctx

val emp : 'a ctx
val get_opt : 'a ctx -> string -> 'a option
val _get_force : Lexing.position -> 'a ctx -> string -> 'a
val add_to_right : 'a. 'a ctx -> ('a, string) Zutils.typed -> 'a ctx
val add_to_rights : 'a. 'a ctx -> ('a, string) Zutils.typed list -> 'a ctx
val ctx_to_list : 'a ctx -> ('a, string) Zutils.typed list
val ctx_to_map : 'a ctx -> 'a Zdatatype.StrMap.t
val ctx_from_list : ('a, string) Zutils.typed list -> 'a ctx
val ctx_from_map : 'a Zdatatype.StrMap.t -> 'a ctx

val map_ctx_typed :
  (('a, string) Zutils.typed -> ('b, string) Zutils.typed) -> 'a ctx -> 'b ctx

val map_ctx : ('a -> 'b) -> 'a ctx -> 'b ctx

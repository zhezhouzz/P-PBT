open To_id

type ast = string

let from_pattern = id_of_pattern
let from_expr = id_of_expr
let layout (label : ast) = label

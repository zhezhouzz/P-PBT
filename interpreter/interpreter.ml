include Eval
open Runtime
open Language

let interpret env term =
  let runtime = init_runtime env default_sample_domain in
  let runtime, _ = eval_until_consistent (runtime, term) in
  let () =
    Pp.printf "@{<bold>trace:@}\n@{<orange>%s@}\n" (layout_trace runtime.trace)
  in
  ()

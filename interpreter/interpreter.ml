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

let interpret_sample env term total =
  let runtime = init_runtime env default_sample_domain in
  let num = eval_sample (runtime, term) total in
  let () =
    Pp.printf "@{<bold>ratio:@}\n@{<orange>%i/%i = %f@}\n" num total
      (float_of_int (100 * num) /. float_of_int total)
  in
  ()

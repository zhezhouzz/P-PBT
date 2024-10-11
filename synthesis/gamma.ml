open Language

type gamma = { bvs : (Nt.nt, string) typed list; bprop : Nt.nt prop }

let mem { bvs; _ } = tv_mem bvs
let not_mem { bvs; _ } = tv_not_mem bvs
let emp = { bvs = []; bprop = mk_true }
let layout { bvs; bprop } = spf "{%s | %s}" (layout_qvs bvs) (layout_prop bprop)

let check_valid { bvs; bprop } prop =
  let q = smart_forall bvs @@ smart_implies bprop prop in
  let res = Prover.check_valid q in
  let () =
    Pp.printf "@{<bold> check valid: @} %s :: %b\n" (layout_prop q) res
  in
  res

let check_sat { bvs; bprop } prop =
  let q = smart_forall bvs @@ smart_implies bprop prop in
  let res = Prover.check_sat_bool q in
  let () = Pp.printf "@{<bold> check sat: @} %s :: %b\n" (layout_prop q) res in
  res

spec LsnProgressMonotonically (id: tLsn) {
  atom (a: LsnProgress) :: #lsn == id;
  atom (b: LsnProgress) :: #lsn < id;
  atom (c: eAllRequestsProcessed) :: true;
  regex not ((. \ eAllRequestsProcessed)* ~ a ~ (. \ eAllRequestsProcessed)* ~ b ~ .*)
}
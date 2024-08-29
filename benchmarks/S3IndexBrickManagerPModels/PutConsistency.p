spec maxSqr (key1: tKey) (sqr1: tSqr) {
  atom (respGt: BrickPutResp) :: #key == key1 && #sqr > sqr1;
  atom (respEq: BrickPutResp) :: #key == key1 && #sqr == sqr1;
  regex (not (.* ~ respGt ~ .*)) && (.* ~ respEq ~ .*)
  }

/* The Succuss Resonse of a request id cannot have sequencer less than any previous response (even not success) */
spec PutConsistency (key1: tKey) (rId1: int) (sqr1: tSqr) {
  atom (respSucc: BrickPutResp) :: #key == key1 && #rId == rId1 && #sqr < sqr1 && #responseStatus == DELETESUCCESS;
  regex not ((maxSqrOnKey key1 sqr1) ~ respSucc ~ .*);
  }

spec PutEventually (rId1: int) {
  atom (req: BrickPutReq) :: #rId == rId1;
  atom (resp: BrickPutResp) :: #rId == rId1;
  regex not (.* ~ req ~ (. \ resp)*)
  }

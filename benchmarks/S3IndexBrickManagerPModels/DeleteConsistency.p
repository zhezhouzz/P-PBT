spec maxSqr (key1: tKey) (sqr1: tSqr) {
  atom (respGt: BrickDeleteResp) :: #key == key1 && #sqr > sqr1;
  atom (respEq: BrickDeleteResp) :: #key == key1 && #sqr == sqr1;
  regex (not (.* ~ respGt ~ .*)) && (.* ~ respEq ~ .*)
  }

/* The Succuss Resonse of a request id cannot have sequencer less than any previous response (even not success) */
spec DeleteConsistency (key1: tKey) (rId1: int) (sqr1: tSqr) {
  atom (respSucc: BrickDeleteResp) :: #key == key1 && #rId == rId1 && #sqr < sqr1 && #responseStatus == SUCCESS;
  regex not ((maxSqrOnKey key1 sqr1) ~ respSucc ~ .*);
  }

spec DeleteEventually (rId1: int) {
  atom (req: BrickDeleteReq) :: #rId == rId1;
  atom (resp: BrickDeleteResp) :: #rId == rId1;
  regex not (.* ~ req ~ (. \ resp)*)
  }

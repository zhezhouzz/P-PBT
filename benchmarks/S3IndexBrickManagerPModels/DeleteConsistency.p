spec maxSqr (key: tByteString) (sqr: int) = {
  atom (respGt: eBrickDeleteResp) :: #key == key && #sqr > sqr
  atom (respEq: eBrickDeleteResp) :: #key == key && #sqr == sqr
  regex (not (.* ~ respGt ~ .*)) && (.* ~ respEq ~ .*)
  }

/* The Succuss Resonse of a request id cannot have sequencer less than any previous response (even not success) */
spec DeleteConsistency (key: tByteString) (rId: int) (sqr: int) = {
  atom (respSucc: eBrickDeleteResp) :: #key == key && #rId == rId && #sqr < sqr && status == SUCCESS;
  regex not ((maxSqrOnKey key sqr) ~ respSucc ~ .*);
  }

spec DeleteEventually (rId: int) = {
  atom (req: eBrickDeleteReq) :: #rId == rId
  atom (resp: eBrickDeleteResp) :: #rId == rId
  regex not (.* ~ req ~ (. \ resp)*)
  }

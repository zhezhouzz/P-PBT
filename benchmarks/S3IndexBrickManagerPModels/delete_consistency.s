spec maxSqr (key: tByteString) (sqr: int) = {
  atom (respGt: eBrickDeleteResp) :: #key == key && #sqr > sqr
  atom (respEq: eBrickDeleteResp) :: #key == key && #sqr == sqr
  regex (not (.* ~ respGt ~ .*)) && (.* ~ respEq ~ .*)
  }

spec noRespYet (key: tByteString) (rId: int) = {
  atom (req: eBrickDeleteReq) :: #key == key && #rId == rId
  atom (resp: eBrickDeleteResp) :: #key == key && #rId == rId
  regex (.* ~ req ~ (. \ resp)*)
  }

(* The First and Succuss Resonse of a request id cannot have sequencer less than any previous response (even not success) *)
spec DeleteConsistency (key: tByteString) (rId: int) (sqr: int) = {
  atom (respSucc: eBrickDeleteResp) :: #key == key && #rId == rId && #sqr < sqr && status == SUCCESS;
  regex not ((maxSqrOnKey key sqr && noRespYet key rId) ~ respSucc ~ .*);
  }

spec DeleteEventually (rId: int) = {
  atom (req: eBrickDeleteReq) :: #rId == rId
  atom (resp: eBrickDeleteResp) :: #rId == rId
  regex not (.* ~ req ~ (. \ resp)*)
  }

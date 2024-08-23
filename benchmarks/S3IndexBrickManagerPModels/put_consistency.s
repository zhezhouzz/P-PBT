request event eBrickPutReq (rId: int, key: tByteString)  ;
response event eBrickPutResp (rId: int, key: tByteString, sqr: int) ;

spec maxSqr (key: tByteString) (sqr: int) = {
  atom (respGt: eBrickPutResp) :: #key == key && #sqr > sqr
  atom (respEq: eBrickPutResp) :: #key == key && #sqr == sqr
  regex (not (.* ~ respGt ~ .*)) && (.* ~ respEq ~ .*)
  }

/* The Succuss Resonse of a request id cannot have sequencer less than any previous response (even not success) */
spec PutConsistency (key: tByteString) (rId: int) (sqr: int) = {
  atom (respSucc: eBrickPutResp) :: #key == key && #rId == rId && #sqr < sqr && responseStatus == DELETESUCCESS;
  regex not ((maxSqrOnKey key sqr) ~ respSucc ~ .*);
  }

spec PutEventually (rId: int) = {
  atom (req: eBrickPutReq) :: #rId == rId
  atom (resp: eBrickPutResp) :: #rId == rId
  regex not (.* ~ req ~ (. \ resp)*)
  }
